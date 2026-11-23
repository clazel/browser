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
// - An image draw (item 6.12) is a quad with columns 0xffffffff; its offset is the
//   index of a 12-word record in `draws` (backend.rs, `ImageDraw`), and the filter is
//   computed here: the pixel centre mapped into the source rectangle, then the pixel
//   there (nearest) or the four around it weighted (linear), clamped to the source
//   rectangle. `images` is the image store: one word, red in the low byte, a pixel.
//   No sampler: quad.frag is the twin and says the same.
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
    uint image_bytes;
    uint draw_count;
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

// The premultiplied RGBA, 0 to 1, of pixel (x, y) of the image at byte `offset` that
// is `iw` by `ih`; transparent black outside the image or the store.
static float4 texel(device const uint *images, constant Uniforms &u,
                    uint offset, uint iw, uint ih, int x, int y) {
    if (x < 0 || y < 0 || uint(x) >= iw || uint(y) >= ih) {
        return float4(0.0);
    }
    uint index = (offset >> 2u) + uint(y) * iw + uint(x);
    if (index >= (u.image_bytes >> 2u)) {
        return float4(0.0);
    }
    uint word = images[index];
    return float4(float(word & 255u), float((word >> 8u) & 255u),
                  float((word >> 16u) & 255u), float(word >> 24u)) / 255.0;
}

static float4 image_colour(device const uint *images, device const uint *draws,
                           constant Uniforms &u, uint d, int px, int py) {
    int dx = as_type<int>(draws[d]);
    int dy = as_type<int>(draws[d + 1u]);
    uint dw = draws[d + 2u];
    uint dh = draws[d + 3u];
    int sx = int(draws[d + 4u]);
    int sy = int(draws[d + 5u]);
    uint sw = draws[d + 6u];
    uint sh = draws[d + 7u];
    uint offset = draws[d + 8u];
    uint iw = draws[d + 9u];
    uint ih = draws[d + 10u];
    bool linear = draws[d + 11u] != 0u;
    if (dw == 0u || dh == 0u || sw == 0u || sh == 0u) {
        return float4(0.0);
    }
    // The pixel's centre in the source, in source pixels: s + (2i + 1) * len / 2n.
    float i = float(px - dx);
    float j = float(py - dy);
    float pu = float(sx) + ((2.0 * i + 1.0) * float(sw)) / (2.0 * float(dw));
    float pv = float(sy) + ((2.0 * j + 1.0) * float(sh)) / (2.0 * float(dh));
    int x_last = sx + int(sw) - 1;
    int y_last = sy + int(sh) - 1;
    if (!linear) {
        int x = clamp(int(floor(pu)), sx, x_last);
        int y = clamp(int(floor(pv)), sy, y_last);
        return texel(images, u, offset, iw, ih, x, y);
    }
    float tu = pu - 0.5;
    float tv = pv - 0.5;
    float fu = floor(tu);
    float fv = floor(tv);
    float wu = tu - fu;
    float wv = tv - fv;
    int x0 = clamp(int(fu), sx, x_last);
    int x1 = clamp(int(fu) + 1, sx, x_last);
    int y0 = clamp(int(fv), sy, y_last);
    int y1 = clamp(int(fv) + 1, sy, y_last);
    float4 top = mix(texel(images, u, offset, iw, ih, x0, y0),
                     texel(images, u, offset, iw, ih, x1, y0), wu);
    float4 bottom = mix(texel(images, u, offset, iw, ih, x0, y1),
                        texel(images, u, offset, iw, ih, x1, y1), wu);
    return mix(top, bottom, wv);
}

fragment float4 quad_fragment(Varyings in [[stage_in]],
                              device const uint *quads [[buffer(0)]],
                              device const uchar *atlas [[buffer(1)]],
                              constant Uniforms &u [[buffer(2)]],
                              device const uint *images [[buffer(3)]],
                              device const uint *draws [[buffer(4)]]) {
    uint base = in.quad * 9u;
    uint columns = quads[base + 7u];
    uint colour = quads[base + 8u];
    if (columns == 0xffffffffu) {
        if (quads[base + 6u] >= u.draw_count) {
            return float4(0.0);
        }
        uint d = quads[base + 6u] * 12u;
        return image_colour(images, draws, u, d, int(in.position.x), int(in.position.y));
    }
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
