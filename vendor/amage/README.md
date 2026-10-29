# Vendored AMAGE packages

Copies of the [AMAGE](https://github.com/amage-si) libraries this repo uses,
at fixed commits. They import each other by relative path, so they sit
side by side here. Each keeps its README and licenses (Apache-2.0 or MIT);
tests, docs, examples, benchmarks, Ankra's `probe.bend`, Voltra's compiled
`.spv` shaders (its `shaders/spirv.bend` holds the same words) and its
`native/abi_check.py`, and the packages' agent instruction files are left
out. Ankra and Voltra each include a native bridge in C (`native/`).

| Package | What it does | Commit |
|---|---|---|
| [Runika](https://github.com/amage-si/runika) | Reads TrueType fonts | `f3bbc5e` |
| [Syllo](https://github.com/amage-si/syllo) | Lays out text | `92321fa` |
| [Dithra](https://github.com/amage-si/dithra) | Rasterizes glyph outlines into coverage masks | `2d73790` |
| [Splina](https://github.com/amage-si/splina) | Paths and transforms (used by Runika and Dithra) | `c279d4c` |
| [Chromi](https://github.com/amage-si/chromi) | Draw lists, and their CPU and GPU renderers | `c2334de` |
| [Voltra](https://github.com/amage-si/voltra) | Draws on the GPU with Vulkan, and presents to a window | `667b164` |
| [Ankra](https://github.com/amage-si/ankra) | A native X11 window, its events, and the app loop | `d1b3a62` |

To update one, replace its directory with the same files from a newer
commit and change the commit above.
