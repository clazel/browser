// The fixed fragment shader of clazel-gpu for Vulkan (phase-5.md item 5.17b),
// GLSL 4.50 for SPIR-V (GL_KHR_vulkan_glsl). quad.metal is its Metal twin and
// states the modelling choices. GLSL has no byte buffer, so the atlas is read as
// little-endian 32-bit words and the byte taken from its word. Compiled to
// quad.frag.spv by `cargo xtask shaders`; `cargo xtask check` confirms the two
// agree.
#version 450

layout(std430, set = 0, binding = 0) readonly buffer Quads {
    uint quads[];
};

layout(std430, set = 0, binding = 1) readonly buffer Atlas {
    uint atlas[];
};

layout(push_constant) uniform Uniforms {
    uint width;
    uint height;
    uint quad_count;
    uint atlas_bytes;
} u;

layout(location = 0) flat in uint quad;
layout(location = 0) out vec4 colour_out;

void main() {
    uint base = quad * 9u;
    uint columns = quads[base + 7u];
    uint colour = quads[base + 8u];
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
