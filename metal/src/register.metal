#include <metal_stdlib>
using namespace metal;
using Wide = ulong;
constant uint WORD_LIMIT=63, KNOWN_LIMIT=56, CONSTANT_BITS=60, FEED_BITS=32, FILL_AT=24;
struct Prefix { Wide word, b; uint h, len, k; };
struct Cost { uint loss, base, returns, operations; };
Wide pair_word(uint low, uint high) { return ulong(low)|(ulong(high)<<32); }
uint upper_word(Wide value) { return uint(value>>32); }
bool valid(thread const Prefix &s) {
    return s.h<=4 && s.len<=WORD_LIMIT && s.k<=KNOWN_LIMIT &&
        s.word<(Wide(1)<<s.len) && s.b<(Wide(1)<<CONSTANT_BITS);
}
int advance_known(thread Prefix &s, thread Cost &cost) {
    if (!valid(s)) return -1;
    if ((Wide(1) << s.k)+s.b < 9) return 0;
    bool nonempty=s.len!=0;
    uint first=(!nonempty || (s.word&Wide(1))!=0) ? 3 : 1;
    uint r=uint(s.b&Wide(3));
    if (s.h==0 || s.h==2) {
        if (!nonempty && s.k<1) return 0;
    } else {
        if (s.k<1) return 0;
        if (((r&1)==0 || (s.h==4 && (!nonempty || first==3))) && s.k<2) return 0;
    }
    Wide visible=s.b&((Wide(1)<<s.k)-Wide(1));
    if (s.h==4 && (!nonempty || first==3) && r==0 && visible==0) return 0;
    uint base;
    if (s.h==0 || s.h==2) base=nonempty ? 3 : 2+(r&1);
    else if (s.h==1 || s.h==3) base=2+uint(r==2);
    else if (nonempty && first==1) base=(r&1)!=0 ? 6 : 3+uint(r==2);
    else base=6-uint(r==3);

    bool pop=false;
    uint digits[2]={0,0};
    uint count=0, loss=0, returns=1;
    Wide addition=0;
    if (s.h==0 || s.h==2) {
        addition=1;
        if (nonempty) { s.h=first+uint(s.h==0); pop=true; }
        else { s.h=(s.h==0 ? 3u : 2u)-2*(r&1); loss=1; }
    } else if (s.h==1 || s.h==3) {
        if ((r&1)!=0) { s.h-=1; addition=1; }
        else {
            s.h=first+uint(s.h==1); pop=nonempty;
            if (nonempty) { digits[0]=3; digits[1]=3-r; count=2; }
            else { digits[0]=3-r; count=1; }
            addition=3; loss=2;
        }
    } else if (nonempty && first==1) {
        s.h=3; pop=true;
        if ((r&1)!=0) addition=2;
        else {
            digits[0]=3; digits[1]=3-r; count=2;
            addition=3; loss=2; returns+=uint(r==2);
        }
    } else {
        s.h=1; pop=nonempty;
        uint last=r==3 ? 3 : 1;
        if (nonempty) { digits[0]=3; digits[1]=last; count=2; }
        else { digits[0]=last; count=1; }
        if ((r&1)!=0) addition=3;
        else if (r==2) { addition=8; returns+=1; }
        else addition=Wide(3)*(visible&(~visible+Wide(1)));
        loss=2;
    }
    if (loss>s.k) return -1;
    s.b=(s.b+addition)>>loss; s.k-=loss;
    if (pop) { s.word>>=1; s.len-=1; }
    for (uint i=0; i<count; ++i) {
        if (s.len>=WORD_LIMIT) return -1;
        s.word|=Wide(digits[i]==3)<<s.len; s.len+=1;
    }
    if (cost.loss>0xffffffffu-loss || cost.base>0xffffffffu-base ||
        cost.returns>0xffffffffu-returns || cost.operations==0xffffffffu) return -1;
    cost.loss+=loss; cost.base+=base;
    cost.returns+=returns; cost.operations+=1;
    return 1;
}

uint low_bits(device const uint *input, uint at, uint count, uint words) {
    uint index=at/32, shift=at%32;
    uint value=input[index]>>shift;
    if (shift!=0 && index+1<words) value|=input[index+1]<<(32-shift);
    return count==32 ? value : value&((1u<<count)-1u);
}

bool range_scalar(device const uint *input, uint start, uint end, uint words,
                thread uint &at, thread Prefix &s, thread Cost &cost) {
    for (uint iteration=0; iteration<1000000; ++iteration) {
        if (!valid(s)) return false;
        if (at<end && s.k<=FILL_AT) {
            uint count=min(FEED_BITS,end-at);
            s.b+=Wide(low_bits(input,start+at,count,words))<<s.k;
            s.k+=count; at+=count;
        }
        int outcome=advance_known(s,cost);
        if (outcome<0) return false;
        if (outcome==1) continue;
        if (at==end) return true;
        uint count=min(min(FEED_BITS,KNOWN_LIMIT-s.k),end-at);
        if (count==0) return false;
        s.b+=Wide(low_bits(input,start+at,count,words))<<s.k;
        s.k+=count; at+=count;
    }
    return false;
}

uint byte_hash(ulong key) {
    uint x=uint(key)^(uint(key>>32)*0x9e3779b9u);
    x^=x>>16; x*=0x7feb352du; x^=x>>15;
    return x;
}
uint byte_lookup(thread const Prefix &s, device const ulong *table) {
    if (!valid(s) || s.len>=24 || s.k>=32 || s.b>=(Wide(1)<<27)) return 0xffffffffu;
    ulong key=ulong(s.word)|(ulong(s.len)<<24)|(ulong(s.h)<<29)|
        (ulong(s.k)<<32)|(ulong(s.b)<<37);
    device const uint *header=(device const uint *)table;
    uint mask=header[4]-1, start=byte_hash(key);
    device const uint *slots=header+header[7];
    device const ulong *states=table+header[6];
    for (uint probe=0;probe<header[10];++probe) {
        uint id=slots[(start+probe)&mask];
        if (!id) return 0xffffffffu;
        if (states[id-1]==key) return id-1;
    }
    return 0xffffffffu;
}
Prefix byte_state(ulong key) {
    return Prefix{Wide(key&0xfffffful),Wide(key>>37),uint((key>>29)&7),
        uint((key>>24)&31),uint((key>>32)&31)};
}
int byte_potential(thread const Prefix &s) {
    return int(s.h/2+2*(s.h%2))+4*int(s.len)+int(popcount(s.word));
}
bool byte_generic(device const uint *input,uint start,uint end,uint words,
                  thread uint &at,thread Prefix &s,thread Cost &cost,thread uint &j) {
    uint old_base=cost.base,old_loss=cost.loss;
    int old_phi=byte_potential(s);
    if (!range_scalar(input,start,end,words,at,s,cost)) return false;
    int residual=int(cost.base-old_base)-2*int(cost.loss-old_loss)-old_phi+byte_potential(s);
    if (residual<0 || residual%3!=0) return false;
    j+=uint(residual/3);
    return true;
}
bool range_fast(device const uint *input, uint start, uint end, uint words,
                thread uint &at, thread Prefix &s, thread Cost &cost,
                device const ulong *table) {
    device const uint *header=(device const uint *)table;
    const uint common=header[2];
    device const ulong *states=table+header[6];
    device const uint *rows=(device const uint *)(table+header[8]);
    uint id=byte_lookup(s,table);
    uint initial_at=at,initial_k=s.k,j=0;
    int initial_phi=byte_potential(s);
    Cost added={0,0,0,0};
    while (end-at>=8) {
        if (id<common) {
            uint edge=rows[(id<<8)+low_bits(input,start+at,8,words)];
            j+=(edge>>16)&((1u<<(22-16))-1);
            uint ops=(edge>>22)&63;
            added.operations+=ops;added.returns+=ops+(edge>>28);
            id=edge&((1u<<16)-1);at+=8;
        } else {
            if (id!=0xffffffffu) s=byte_state(states[id]);
            if (!byte_generic(input,start,at+8,words,at,s,added,j)) return false;
            id=byte_lookup(s,table);
        }
    }
    if (id!=0xffffffffu) s=byte_state(states[id]);
    if (!byte_generic(input,start,end,words,at,s,added,j)) return false;
    uint loss=at-initial_at+initial_k-s.k;
    int base=2*int(loss)+initial_phi-byte_potential(s)+3*int(j);
    if (base<0 || cost.loss>0xffffffffu-loss || cost.base>0xffffffffu-uint(base) ||
        cost.returns>0xffffffffu-added.returns || cost.operations>0xffffffffu-added.operations) return false;
    cost.loss+=loss;cost.base+=uint(base);cost.returns+=added.returns;cost.operations+=added.operations;
    return true;
}
void snapshot(device uint *out, thread const Prefix &s, thread const Cost &c,
              uint at, bool success) {
    out[0]=uint(s.word); out[1]=upper_word(s.word);
    out[2]=uint(s.b); out[3]=upper_word(s.b);
    out[4]=s.h; out[5]=s.len; out[6]=s.k; out[7]=0;
    out[8]=c.loss; out[9]=c.base; out[10]=c.returns; out[11]=c.operations;
    out[12]=at; out[13]=uint(success); out[14]=0; out[15]=0;
}

Prefix load_prefix(device const uint *in) {
    Prefix s={pair_word(in[0],in[1]),pair_word(in[2],in[3]),in[4],in[5],in[6]};
    return s;
}

bool same(thread const Prefix &a, thread const Prefix &b) {
    return a.word==b.word && a.b==b.b && a.h==b.h && a.len==b.len && a.k==b.k;
}

kernel void register_links(device const uint *input [[buffer(0)]],
                           device const uint *baselines [[buffer(1)]],
                           device uint *output [[buffer(2)]],
                           constant uint *params [[buffer(3)]],
                           uint index [[thread_position_in_grid]], device const ulong *byte_table [[buffer(4)]]) {
    if (index>=params[2]) return;
    device uint *out=output+16*index;
    out[13]=0; out[14]=0;
    device const uint *block=baselines+116*index;
    if (block[0]!=1 || block[1]<1 || block[1]>7) return;
    device const uint *end=block+4+16*(block[1]-1);
    Prefix endpoint=load_prefix(end);
    Cost cost={0,0,0,0};
    snapshot(out,endpoint,cost,end[12],false); out[14]=1;
    Prefix state;
    if (index==0) {
        state=Prefix{pair_word(params[6],params[7]),0,params[4],params[5],0};
    } else {
        device const uint *previous=baselines+116*(index-1);
        if (previous[0]!=1 || previous[1]<1 || previous[1]>7) return;
        state=load_prefix(previous+4+16*(previous[1]-1));
    }
    if (state.h==2 && state.word==0 && state.len==0 && state.k==0 && state.b==0) {
        cost=Cost{end[8],end[9],end[10],end[11]};
        snapshot(out,endpoint,cost,end[12],true); out[14]=1; return;
    }
    uint at=0, start=index*params[1];
    for (uint i=0; i<block[1]; ++i) {
        device const uint *point=block+4+16*i;
        if (!range_fast(input,start,point[12],params[3],at,state,cost, byte_table)) return;
        Prefix proposed=load_prefix(point);
        if (!same(state,proposed)) continue;
        uint residual[4];
        for (uint j=0; j<4; ++j) {
            if (end[8+j]<point[8+j]) return;
            residual[j]=end[8+j]-point[8+j];
        }
        if (cost.loss>0xffffffffu-residual[0] || cost.base>0xffffffffu-residual[1] ||
            cost.returns>0xffffffffu-residual[2] || cost.operations>0xffffffffu-residual[3]) return;
        cost.loss+=residual[0]; cost.base+=residual[1];
        cost.returns+=residual[2]; cost.operations+=residual[3];
        snapshot(out,endpoint,cost,end[12],true); out[14]=1; return;
    }
}

kernel void register_blocks(device const uint *input [[buffer(0)]],
                            device uint *output [[buffer(1)]],
                            constant uint *params [[buffer(2)]],
                            uint index [[thread_position_in_grid]], device const ulong *byte_table [[buffer(4)]]) {
    uint bits=params[0], block_bits=params[1], blocks=params[2];
    if (index>=blocks) return;
    device uint *out=output+116*index;
    out[0]=0; out[1]=0; out[2]=0; out[3]=0;
    uint start=index*block_bits, length=min(bits-1-start,block_bits);
    Prefix state={0,0,2,0,0}; Cost cost={0,0,0,0};
    uint at=0, used=0;
    const uint stops[7]={64,128,256,512,1024,2048,length};
    for (uint i=0; i<7; ++i) {
        if (i<6 && stops[i]>=length) continue;
        uint end=stops[i];
        if (!range_fast(input,start,end,params[3],at,state,cost, byte_table)) return;
        snapshot(out+4+16*used,state,cost,at,true); used+=1;
    }
    out[1]=used; out[0]=1;
}

bool checked_link(device const uint *row, uint length, thread Prefix &s) {
    if (row[13]>1 || row[14]!=1 || row[12]!=length ||
        row[4]>4 || row[5]>WORD_LIMIT || row[6]>KNOWN_LIMIT) return false;
    s=load_prefix(row);
    return valid(s);
}

bool add_cost(thread Cost &cost, device const uint *row) {
    if (cost.loss>0xffffffffu-row[8] || cost.base>0xffffffffu-row[9] ||
        cost.returns>0xffffffffu-row[10] || cost.operations>0xffffffffu-row[11]) return false;
    cost.loss+=row[8]; cost.base+=row[9];
    cost.returns+=row[10]; cost.operations+=row[11];
    return true;
}

kernel void register_fold(device const uint *input [[buffer(0)]],
                          device const uint *links [[buffer(1)]],
                          device uint *output [[buffer(2)]],
                          constant uint *params [[buffer(3)]],
                          uint index [[thread_position_in_grid]]) {
    uint begin=index*params[8], finish=min(begin+params[8],params[2]);
    if (begin>=finish) return;
    device uint *out=output+32*index;
    out[13]=0; out[14]=0;
    Prefix seed={0,0,2,0,0};
    if (begin==0) {
        seed=Prefix{pair_word(params[6],params[7]),0,params[4],params[5],0};
    } else {
        if (!checked_link(links+16*(begin-1),params[1],seed)) return;
    }
    if (!valid(seed)) return;
    Prefix state=seed;
    Cost cost={0,0,0,0};
    for (uint i=begin; i<finish; ++i) {
        device const uint *row=links+16*i;
        uint start=i*params[1], length=min(params[0]-1-start,params[1]);
        Prefix endpoint;
        if (!checked_link(row,length,endpoint) || row[13]!=1 || !add_cost(cost,row)) return;
        state=endpoint;
    }
    snapshot(out,state,cost,min(params[0]-1,finish*params[1])-begin*params[1],true);
    out[14]=1; out[15]=finish-begin;
    Cost unused={0,0,0,0};
    snapshot(out+16,seed,unused,0,true);
    out[24]=finish-begin; out[25]=0;
}
