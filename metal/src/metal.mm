#import <Foundation/Foundation.h>
#import <Metal/Metal.h>
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <memory>
#include <new>
#include <cstddef>
#include <gmp.h>
#include <dispatch/dispatch.h>
#include <array>
#include <cassert>
#include <pthread/qos.h>
#if defined(__aarch64__)
#include <arm_neon.h>
#endif

static_assert(GMP_NUMB_BITS == 64 && sizeof(mp_limb_t) == 8);
static_assert(sizeof(__mpz_struct) == 16 && offsetof(__mpz_struct, _mp_d) == 8);
static_assert(offsetof(__mpz_struct, _mp_alloc) == 0 && offsetof(__mpz_struct, _mp_size) == 4);

extern "C" void tm_prepare_runtime() {
    pthread_set_qos_class_self_np(QOS_CLASS_USER_INITIATED,0);
}

extern "C" uint64_t tm_mod3(const uint64_t *limbs, size_t count) {
    const auto *p = reinterpret_cast<const unsigned char *>(limbs);
    size_t remaining = count*2;
    uint64_t residue = 0;
    while (remaining) {
        size_t n = std::min(remaining, size_t(1)<<28);
        remaining -= n;
        uint64_t sum = 0;
#if defined(__aarch64__)
        uint64x2_t a = vdupq_n_u64(0), b = a, c = a, d = a;
        while (n >= 16) {
            a = vpadalq_u32(a, vreinterpretq_u32_u8(vld1q_u8(p)));
            b = vpadalq_u32(b, vreinterpretq_u32_u8(vld1q_u8(p+16)));
            c = vpadalq_u32(c, vreinterpretq_u32_u8(vld1q_u8(p+32)));
            d = vpadalq_u32(d, vreinterpretq_u32_u8(vld1q_u8(p+48)));
            p += 64; n -= 16;
        }
        sum = vaddvq_u64(vaddq_u64(vaddq_u64(a,b),vaddq_u64(c,d)));
#endif
        while (n--) {
            uint32_t digit;
            std::memcpy(&digit,p,sizeof(digit));
            sum+=digit; p+=sizeof(digit);
        }
        residue = (residue + sum%3)%3;
    }
    return residue;
}

struct LimbJob {
    mp_limb_t *out;
    const mp_limb_t *input;
    size_t count, chunk;
    mp_limb_t slope;
    unsigned shift;
    std::array<mp_limb_t, 32> boundary{};
};
static void multiply_chunk(void *context, size_t i) {
    auto &j = *static_cast<LimbJob *>(context);
    const size_t start = i*j.chunk, n = std::min(j.chunk,j.count-start);
    if (j.slope == 1) {
        std::memcpy(j.out+start,j.input+start,n*sizeof(mp_limb_t));
        j.boundary[i] = 0;
    } else {
        j.boundary[i] = mpn_mul_1(j.out+start,j.input+start,n,j.slope);
    }
}
static void shift_chunk(void *context, size_t i) {
    auto &j = *static_cast<LimbJob *>(context);
    const size_t start = i*j.chunk, n = std::min(j.chunk,j.count-start);
    mpn_rshift(j.out+start,j.out+start,n,j.shift);
    j.out[start+n-1] |= j.boundary[i] << (64-j.shift);
}
static void prepare_chunk(void *context, size_t i) {
    auto &j = *static_cast<LimbJob *>(context);
    const size_t start=i*j.chunk, n=std::min(j.chunk,j.count-start);
    if (j.shift) {
        mpn_rshift(j.out+start,j.input+start,n,j.shift);
        if (start+n<j.count) j.out[start+n-1] |= j.input[start+n] << (64-j.shift);
    } else {
        std::memcpy(j.out+start,j.input+start,n*sizeof(mp_limb_t));
    }
}

extern "C" bool tm_set_dyadic(mpz_ptr out, mpz_srcptr input, int64_t slope,
                              int64_t constant, uint64_t shift) {
    if (input->_mp_size < 16384 || slope <= 0 || shift >= 64) return false;
    const size_t n = size_t(input->_mp_size);
    mp_limb_t *dest = mpz_limbs_write(out,n+1);
    LimbJob job{dest,input->_mp_d,n,(n+7)/8,mp_limb_t(slope),0,{}};
    const size_t chunks = (n+job.chunk-1)/job.chunk;
    auto queue = dispatch_get_global_queue(QOS_CLASS_USER_INITIATED,0);
    dispatch_apply_f(chunks,queue,&job,multiply_chunk);
    mp_limb_t carry = 0;
    for (size_t i=0; i<chunks; ++i) {
        const size_t start=i*job.chunk, count=std::min(job.chunk,n-start);
        const mp_limb_t overflow = carry ? mpn_add_1(dest+start,dest+start,count,carry) : 0;
        carry = job.boundary[i]+overflow;
    }
    dest[n] = carry;
    mpz_limbs_finish(out,n+(carry!=0));
    if (constant >= 0) mpz_add_ui(out,out,uint64_t(constant));
    else mpz_sub_ui(out,out,uint64_t(-(constant+1))+1);
    if (!mpz_divisible_2exp_p(out,shift)) return false;
    if (shift) {
        const size_t count = size_t(out->_mp_size);
        job.out=out->_mp_d; job.count=count; job.chunk=(count+7)/8; job.shift=unsigned(shift);
        const size_t shifts=(count+job.chunk-1)/job.chunk;
        for (size_t i=0; i<shifts; ++i) {
            const size_t end=std::min((i+1)*job.chunk,count);
            job.boundary[i]=end<count ? job.out[end] : 0;
        }
        dispatch_apply_f(shifts,queue,&job,shift_chunk);
        mpz_limbs_finish(out,count-(job.out[count-1]==0));
    }
    return true;
}

struct MetalState {
    id<MTLDevice> device;
    id<MTLCommandQueue> queue;
    id<MTLComputePipelineState> blocks, links, fold;
    id<MTLBuffer> input, output, baseline, folded, byte_table;
};

static void report(char *out, size_t size, NSString *message) {
    if (out && size) std::snprintf(out, size, "%s", message.UTF8String ?: "Metal initialization failed");
}

extern "C" void *tm_metal_create(const char *shader,
                                const uint8_t *byte_table, size_t byte_table_size,
                                char *error, size_t size) {
    @autoreleasepool {
        @try {
            auto state = std::unique_ptr<MetalState>(new (std::nothrow) MetalState{});
            if (!state) { report(error, size, @"Cannot allocate Metal context"); return nullptr; }
            state->device = MTLCreateSystemDefaultDevice();
            state->queue = [state->device newCommandQueue];
            if (!state->device || !state->queue) {
                report(error, size, @"No Metal device or command queue"); return nullptr;
            }
            {
                state->byte_table=[state->device newBufferWithBytes:byte_table length:byte_table_size
                    options:MTLResourceStorageModeShared];
                if (!state->byte_table) {report(error,size,@"Cannot allocate byte transducer");return nullptr;}
            }
            NSError *failure = nil;
            NSString *source = [NSString stringWithUTF8String:shader];
            if (!source) { report(error, size, failure.localizedDescription); return nullptr; }
            id<MTLLibrary> library = [state->device newLibraryWithSource:source options:nil error:&failure];
            if (!library) { report(error, size, failure.localizedDescription); return nullptr; }
            id<MTLFunction> blocks = [library newFunctionWithName:@"register_blocks"];
            id<MTLFunction> links = [library newFunctionWithName:@"register_links"];
            if (!blocks || !links) { report(error, size, @"Missing Metal register kernels"); return nullptr; }
            state->blocks = [state->device newComputePipelineStateWithFunction:blocks error:&failure];
            if (!state->blocks) { report(error, size, failure.localizedDescription); return nullptr; }
            state->links = [state->device newComputePipelineStateWithFunction:links error:&failure];
            if (!state->links) { report(error, size, failure.localizedDescription); return nullptr; }
            id<MTLFunction> fold = [library newFunctionWithName:@"register_fold"];
            if (!fold) { report(error, size, @"Missing register fold kernel"); return nullptr; }
            state->fold = [state->device newComputePipelineStateWithFunction:fold error:&failure];
            if (!state->fold) { report(error, size, failure.localizedDescription); return nullptr; }
            return state.release();
        } @catch (NSException *exception) {
            report(error, size, exception.reason); return nullptr;
        }
    }
}

extern "C" void tm_metal_destroy(void *context) {
    @autoreleasepool { delete static_cast<MetalState *>(context); }
}

static bool reserve(id<MTLBuffer> __strong &buffer, size_t bytes, id<MTLDevice> device) {
    if (buffer && buffer.length >= bytes) return true;
    const size_t maximum = device.maxBufferLength;
    if (bytes > maximum) return false;
    size_t capacity = 4096;
    while (capacity < bytes) {
        if (capacity > maximum/2) { capacity = bytes; break; }
        capacity *= 2;
    }
    capacity = std::min(capacity, maximum);
    id<MTLBuffer> replacement = [device newBufferWithLength:capacity options:MTLResourceStorageModeShared];
    if (!replacement) return false;
    buffer = replacement;
    return true;
}

extern "C" bool tm_metal_query(void *context, const uint64_t *words, uint32_t source_bits,
                               bool entry,
                               uint32_t head, uint32_t len, uint64_t word,
                               const uint32_t **output, size_t *output_words,
                               const uint64_t **prepared, uint32_t *prepared_bits,
                               const uint32_t **links) {
    @autoreleasepool {
        auto &s = *static_cast<MetalState *>(context);
        constexpr uint32_t block_bits=4096, fold_blocks=32, threadgroup=32;
        *output = nullptr; *output_words = 0;
        *prepared = nullptr; *prepared_bits = 0;
        *links = nullptr;
        constexpr uint64_t maximum_bits = (uint64_t(1)<<32)-(uint64_t(1)<<20);
        if (source_bits>maximum_bits) return false;
        const size_t source_words=(size_t(source_bits)+63)/64;
        if (!source_words || !reserve(s.input,(source_words+1)*8,s.device)) return false;
        auto *dest=static_cast<mp_limb_t *>(s.input.contents);
        const auto *source=reinterpret_cast<const mp_limb_t *>(words);
        const unsigned shift=entry && (source[0]&1)==0 ? 1 : 0;
        LimbJob job{dest,source,source_words,(source_words+7)/8,1,shift,{}};
        if (source_words>=16384) {
            dispatch_apply_f((source_words+job.chunk-1)/job.chunk,
                dispatch_get_global_queue(QOS_CLASS_USER_INITIATED,0),&job,prepare_chunk);
        } else {
            job.chunk=source_words; prepare_chunk(&job,0);
        }
        size_t n=source_words;
        if (entry) {
            dest[n]=mpn_add_1(dest,dest,n,shift ? 6 : 10);
            n+=dest[n]!=0;
        }
        while (n && dest[n-1]==0) --n;
        if (!n) return false;
        const uint64_t wide_bits=64*(n-1)+64-__builtin_clzll(dest[n-1]);
        if (wide_bits>maximum_bits) return false;
        const uint32_t bits=uint32_t(wide_bits);
        *prepared=reinterpret_cast<const uint64_t *>(dest); *prepared_bits=bits;
        const uint32_t tasks = (bits-1+block_bits-1)/block_bits;
        if (!tasks) return true;
        const size_t count = size_t(tasks)*16;
        if (count > 134217728) return false;
        const uint32_t input_words = (bits+31)/32;
        if (!reserve(s.output, count*4, s.device) ||
            !reserve(s.baseline, size_t(tasks)*116*4, s.device)) return false;
        const uint32_t groups = (tasks+fold_blocks-1)/fold_blocks;
        if (!reserve(s.folded,size_t(groups)*32*4,s.device)) return false;
        const uint32_t parameters[9] = {bits, block_bits, tasks, input_words,
                                       head, len, uint32_t(word), uint32_t(word>>32),fold_blocks};
        id<MTLCommandBuffer> command = [s.queue commandBuffer];
        id<MTLComputeCommandEncoder> encoder = [command computeCommandEncoder];
        if (!command || !encoder) return false;
        const MTLSize threads = MTLSizeMake(tasks, 1, 1);
        const uint32_t maximum=uint32_t(std::min(s.blocks.maxTotalThreadsPerThreadgroup,
                                                 s.links.maxTotalThreadsPerThreadgroup));
        const MTLSize group = MTLSizeMake(std::min({threadgroup,tasks,maximum}), 1, 1);
        [encoder setComputePipelineState:s.blocks];
        [encoder setBuffer:s.input offset:0 atIndex:0];
        [encoder setBuffer:s.baseline offset:0 atIndex:1];
        [encoder setBytes:parameters length:sizeof(parameters) atIndex:2];
        [encoder setBuffer:s.byte_table offset:0 atIndex:4];
        [encoder dispatchThreads:threads threadsPerThreadgroup:group];
        [encoder endEncoding];
        encoder = [command computeCommandEncoder];
        if (!encoder) return false;
        [encoder setComputePipelineState:s.links];
        [encoder setBuffer:s.input offset:0 atIndex:0];
        [encoder setBuffer:s.baseline offset:0 atIndex:1];
        [encoder setBuffer:s.output offset:0 atIndex:2];
        [encoder setBytes:parameters length:sizeof(parameters) atIndex:3];
        [encoder setBuffer:s.byte_table offset:0 atIndex:4];
        [encoder dispatchThreads:threads threadsPerThreadgroup:group];
        [encoder endEncoding];
        {
            encoder = [command computeCommandEncoder];
            if (!encoder) return false;
            [encoder setComputePipelineState:s.fold];
            [encoder setBuffer:s.input offset:0 atIndex:0];
            [encoder setBuffer:s.output offset:0 atIndex:1];
            [encoder setBuffer:s.folded offset:0 atIndex:2];
            [encoder setBytes:parameters length:sizeof(parameters) atIndex:3];
            [encoder dispatchThreads:MTLSizeMake(groups,1,1)
                threadsPerThreadgroup:MTLSizeMake(std::min({threadgroup,groups,
                    uint32_t(s.fold.maxTotalThreadsPerThreadgroup)}),1,1)];
            [encoder endEncoding];
        }
        [command commit];
        [command waitUntilCompleted];
        if (command.status != MTLCommandBufferStatusCompleted) return false;
        *output = static_cast<const uint32_t *>(s.folded.contents);
        *output_words = size_t(groups)*32;
        *links = static_cast<const uint32_t *>(s.output.contents);
        return true;
    }
}
