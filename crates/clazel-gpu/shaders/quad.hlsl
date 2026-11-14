// The fixed shaders of clazel-gpu for Direct3D 12 (phase-5.md item 5.17b), in
// HLSL for shader model 5.0. quad.metal is their Metal twin and states the
// modelling choices; quad.vert and quad.frag are the Vulkan twins. These compute
// the same, with three differences that are Direct3D's:
//
// - Normalized device y points up, as on Metal, so y is flipped.
// - SV_InstanceID counts from 0 in every draw, whatever the draw's first
//   instance is (Microsoft Learn, "Semantics": it is not offset by
//   StartInstanceLocation), so the backend passes the draw's first quad as
//   `first_instance` and the shader adds it.
// - The buffers are structured buffers of 32-bit words bound as root shader
//   resource views, which carry no length, so Direct3D bounds no read: the
//   bounds below (`quad_count`, `atlas_bytes`) are the only ones, as
//   crates/clazel-gpu/src/backend.rs says of every backend. The atlas is read as
//   little-endian words and the byte taken from its word, as in quad.frag.
//
// Compiled to quad.hlsl.vs.dxbc (entry quad_vertex, vs_5_0) and
// quad.hlsl.ps.dxbc (entry quad_fragment, ps_5_0) by vkd3d-compiler;
// xtask/src/shaders.rs states the version and compares where it is installed.

cbuffer Uniforms : register(b0) {
    uint width;
    uint height;
    uint quad_count;
    uint atlas_bytes;
    uint first_instance;
};

StructuredBuffer<uint> quads : register(t0);
StructuredBuffer<uint> atlas : register(t1);

struct Varyings {
    float4 position : SV_Position;
    nointerpolation uint quad : QUAD;
};

Varyings quad_vertex(uint vid : SV_VertexID, uint instance : SV_InstanceID) {
    Varyings o;
    uint iid = instance + first_instance;
    o.quad = iid;
    if (iid >= quad_count || vid >= 6u) {
        o.position = float4(0.0, 0.0, 2.0, 1.0);
        return o;
    }
    uint base = iid * 9u;
    // Two triangles: (x0,y0) (x1,y0) (x0,y1), (x1,y0) (x1,y1) (x0,y1).
    bool right = vid == 1u || vid == 3u || vid == 4u;
    bool bottom = vid == 2u || vid == 4u || vid == 5u;
    float x = float(int(quads[base + (right ? 2u : 0u)]));
    float y = float(int(quads[base + (bottom ? 3u : 1u)]));
    o.position = float4(2.0 * x / float(width) - 1.0,
                        1.0 - 2.0 * y / float(height), 0.0, 1.0);
    return o;
}

float4 quad_fragment(Varyings i) : SV_Target {
    uint base = i.quad * 9u;
    uint columns = quads[base + 7u];
    uint colour = quads[base + 8u];
    float k = 1.0;
    if (columns != 0u) {
        int px = int(i.position.x);
        int py = int(i.position.y);
        uint column = uint(px - int(quads[base + 4u]));
        uint row = uint(py - int(quads[base + 5u]));
        uint index = quads[base + 6u] + row * columns + column;
        if (index < atlas_bytes) {
            uint word = atlas[index >> 2u];
            k = float((word >> ((index & 3u) * 8u)) & 255u) / 255.0;
        } else {
            k = 0.0;
        }
    }
    float4 c = float4(float((colour >> 16u) & 255u), float((colour >> 8u) & 255u),
                      float(colour & 255u), float(colour >> 24u)) / 255.0;
    return c * k;
}
