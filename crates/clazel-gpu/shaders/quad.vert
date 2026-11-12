// The fixed vertex shader of clazel-gpu for Vulkan (phase-5.md item 5.17b), GLSL
// 4.50 for SPIR-V (GL_KHR_vulkan_glsl). quad.metal is its Metal twin and states
// the modelling choices; this computes the same, except that Vulkan's normalized
// device y points down, so y is not flipped. Compiled to quad.vert.spv by
// `cargo xtask shaders`; `cargo xtask check` confirms the two agree.
#version 450

layout(std430, set = 0, binding = 0) readonly buffer Quads {
    uint quads[];
};

layout(push_constant) uniform Uniforms {
    uint width;
    uint height;
    uint quad_count;
    uint atlas_bytes;
} u;

layout(location = 0) flat out uint quad;

void main() {
    uint vid = uint(gl_VertexIndex);
    uint iid = uint(gl_InstanceIndex);
    quad = iid;
    if (iid >= u.quad_count || vid >= 6u) {
        gl_Position = vec4(0.0, 0.0, 2.0, 1.0);
        return;
    }
    uint base = iid * 9u;
    // Two triangles: (x0,y0) (x1,y0) (x0,y1), (x1,y0) (x1,y1) (x0,y1).
    bool right = vid == 1u || vid == 3u || vid == 4u;
    bool bottom = vid == 2u || vid == 4u || vid == 5u;
    float x = float(int(quads[base + (right ? 2u : 0u)]));
    float y = float(int(quads[base + (bottom ? 3u : 1u)]));
    gl_Position = vec4(2.0 * x / float(u.width) - 1.0,
                       2.0 * y / float(u.height) - 1.0, 0.0, 1.0);
}
