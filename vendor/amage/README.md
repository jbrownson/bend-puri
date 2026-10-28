# Vendored AMAGE packages

Copies of the [AMAGE](https://github.com/amage-si) libraries this repo uses,
at fixed commits. They import each other by relative path, so they sit
side by side here. Each keeps its README and licenses (Apache-2.0 or MIT);
tests, docs, examples, the GPU renderer (`Chromi/gpu.bend`, which needs
Voltra) and the packages' agent instruction files are left out.

| Package | What it does | Commit |
|---|---|---|
| [Runika](https://github.com/amage-si/runika) | Reads TrueType fonts | `f3bbc5e` |
| [Syllo](https://github.com/amage-si/syllo) | Lays out text | `92321fa` |
| [Dithra](https://github.com/amage-si/dithra) | Rasterizes glyph outlines into coverage masks | `2d73790` |
| [Splina](https://github.com/amage-si/splina) | Paths and transforms (used by Runika and Dithra) | `c279d4c` |
| [Chromi](https://github.com/amage-si/chromi) | Draw lists and the CPU renderer | `c2334de` |

To update one, replace its directory with the same files from a newer
commit and change the commit above.
