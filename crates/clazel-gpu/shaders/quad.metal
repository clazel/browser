// The fixed shaders of clazel-gpu for Metal (phase-5.md item 5.17b), in the Metal
// Shading Language, Apple's "Metal Shading Language Specification" version 3.0.
// GLSL twins for Vulkan: quad.vert and quad.frag, which must compute the same.
//
// Modelling choices (crates/clazel-gpu/src/backend.rs states them in full):
// - One quad per instance, six vertices, read from `quads` by instance index: 9
//   words per quad, x0 y0 x1 y1 origin_x origin_y offset columns colour, the
//   signed ones two's complement. No vertex format, no sampler.
// - A fill has columns 0 and full coverage; a mask's coverage is one byte per
//   pixel in `atlas`, at offset + row * columns + column.
// - Reads are bounded here: an instance at or past quad_count is placed behind
//   the far plane and draws nothing; a coverage index at or past atlas_bytes
//   reads 0.
// - Output is the premultiplied colour times coverage; the pipeline blends it
//   source-over (one, one minus source alpha) into an RGBA8Unorm target, with
//   no sRGB conversion.

#include <metal_stdlib>
using namespace metal;

struct Uniforms {
    uint width;
    uint height;
    uint quad_count;
    uint atlas_bytes;
};

struct Varyings {
    float4 position [[position]];
    uint quad [[flat]];
};

vertex Varyings quad_vertex(uint vid [[vertex_id]],
                            uint iid [[instance_id]],
                            device const uint *quads [[buffer(0)]],
                            constant Uniforms &u [[buffer(2)]]) {
    Varyings out;
    out.quad = iid;
    if (iid >= u.quad_count || vid >= 6u) {
        out.position = float4(0.0, 0.0, 2.0, 1.0);
        return out;
    }
    uint base = iid * 9u;
    // Two triangles: (x0,y0) (x1,y0) (x0,y1), (x1,y0) (x1,y1) (x0,y1).
    bool right = vid == 1u || vid == 3u || vid == 4u;
    bool bottom = vid == 2u || vid == 4u || vid == 5u;
    float x = float(as_type<int>(quads[base + (right ? 2u : 0u)]));
    float y = float(as_type<int>(quads[base + (bottom ? 3u : 1u)]));
    out.position = float4(2.0 * x / float(u.width) - 1.0,
                          1.0 - 2.0 * y / float(u.height), 0.0, 1.0);
    return out;
}

fragment float4 quad_fragment(Varyings in [[stage_in]],
                              device const uint *quads [[buffer(0)]],
                              device const uchar *atlas [[buffer(1)]],
                              constant Uniforms &u [[buffer(2)]]) {
    uint base = in.quad * 9u;
    uint columns = quads[base + 7u];
    uint colour = quads[base + 8u];
    float k = 1.0;
    if (columns != 0u) {
        int px = int(in.position.x);
        int py = int(in.position.y);
        uint column = uint(px - as_type<int>(quads[base + 4u]));
        uint row = uint(py - as_type<int>(quads[base + 5u]));
        uint index = quads[base + 6u] + row * columns + column;
        k = index < u.atlas_bytes ? float(atlas[index]) / 255.0 : 0.0;
    }
    float4 c = float4(float((colour >> 16u) & 255u), float((colour >> 8u) & 255u),
                      float(colour & 255u), float(colour >> 24u)) / 255.0;
    return c * k;
}
