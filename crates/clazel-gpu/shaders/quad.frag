// The fixed fragment shader of clazel-gpu for Vulkan (phase-5.md item 5.17b and
// phase-6.md item 6.12), GLSL 4.50 for SPIR-V (GL_KHR_vulkan_glsl). quad.metal is
// its Metal twin and states the modelling choices. GLSL has no byte buffer, so the
// atlas is read as little-endian 32-bit words and the byte taken from its word; the
// image store is words already (a pixel is one word, red in the low byte). Compiled
// to quad.frag.spv by `cargo xtask tables`; `cargo xtask check` confirms the two
// agree.
//
// A quad with `columns` 0xffffffff is an image draw: its `offset` is the index of
// a 12-word record in `draws` (crates/clazel-gpu/src/backend.rs, `ImageDraw`), and
// this shader does the filtering: the pixel's centre is mapped into the source
// rectangle and the pixel there taken (nearest) or the four around it weighted
// (linear), clamped to the source rectangle.
#version 450

layout(std430, set = 0, binding = 0) readonly buffer Quads {
    uint quads[];
};

layout(std430, set = 0, binding = 1) readonly buffer Atlas {
    uint atlas[];
};

layout(std430, set = 0, binding = 2) readonly buffer Images {
    uint images[];
};

layout(std430, set = 0, binding = 3) readonly buffer Draws {
    uint draws[];
};

layout(push_constant) uniform Uniforms {
    uint width;
    uint height;
    uint quad_count;
    uint atlas_bytes;
    uint image_bytes;
    uint draw_count;
} u;

layout(location = 0) flat in uint quad;
layout(location = 0) out vec4 colour_out;

// The premultiplied RGBA, 0 to 1, of pixel (x, y) of the image at byte `offset`
// that is `iw` by `ih`; transparent black outside the image or the store.
vec4 texel(uint offset, uint iw, uint ih, int x, int y) {
    if (x < 0 || y < 0 || uint(x) >= iw || uint(y) >= ih) {
        return vec4(0.0);
    }
    uint index = (offset >> 2u) + uint(y) * iw + uint(x);
    if (index >= (u.image_bytes >> 2u)) {
        return vec4(0.0);
    }
    uint word = images[index];
    return vec4(float(word & 255u), float((word >> 8u) & 255u),
                float((word >> 16u) & 255u), float(word >> 24u)) / 255.0;
}

// The image draw `d` (a record's first word) at pixel (px, py), as the filter
// defines it.
vec4 image_colour(uint d, int px, int py) {
    int dx = int(draws[d]);
    int dy = int(draws[d + 1u]);
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
        return vec4(0.0);
    }
    // The pixel's centre in the source, in source pixels: s + (2i + 1) · len / 2n.
    float i = float(px - dx);
    float j = float(py - dy);
    float pu = float(sx) + ((2.0 * i + 1.0) * float(sw)) / (2.0 * float(dw));
    float pv = float(sy) + ((2.0 * j + 1.0) * float(sh)) / (2.0 * float(dh));
    int x_last = sx + int(sw) - 1;
    int y_last = sy + int(sh) - 1;
    if (!linear) {
        int x = clamp(int(floor(pu)), sx, x_last);
        int y = clamp(int(floor(pv)), sy, y_last);
        return texel(offset, iw, ih, x, y);
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
    vec4 top = mix(texel(offset, iw, ih, x0, y0), texel(offset, iw, ih, x1, y0), wu);
    vec4 bottom = mix(texel(offset, iw, ih, x0, y1), texel(offset, iw, ih, x1, y1), wu);
    return mix(top, bottom, wv);
}

void main() {
    uint base = quad * 9u;
    uint columns = quads[base + 7u];
    uint colour = quads[base + 8u];
    if (columns == 0xffffffffu) {
        uint d = quads[base + 6u] * 12u;
        if (quads[base + 6u] >= u.draw_count) {
            colour_out = vec4(0.0);
            return;
        }
        colour_out = image_colour(d, int(gl_FragCoord.x), int(gl_FragCoord.y));
        return;
    }
    float k = 1.0;
    if (columns != 0u) {
        int px = int(gl_FragCoord.x);
        int py = int(gl_FragCoord.y);
        uint column = uint(px - int(quads[base + 4u]));
        uint row = uint(py - int(quads[base + 5u]));
        uint index = quads[base + 6u] + row * columns + column;
        if (index < u.atlas_bytes) {
            uint word = atlas[index >> 2u];
            k = float((word >> ((index & 3u) * 8u)) & 255u) / 255.0;
        } else {
            k = 0.0;
        }
    }
    vec4 c = vec4(float((colour >> 16u) & 255u), float((colour >> 8u) & 255u),
                  float(colour & 255u), float(colour >> 24u)) / 255.0;
    colour_out = c * k;
}
