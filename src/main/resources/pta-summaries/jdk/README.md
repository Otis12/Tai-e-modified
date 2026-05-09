# JDK Summary Catalog

This catalog is used only for the JDK summary-only boundary in PTA.
It models selected JDK platform methods when `jdk-analysis-mode: summary-only`
skips JDK method bodies.

Scope:

- The first stage covers JDK platform APIs only.
- Third-party libraries such as Spring, MyBatis, FastJSON, Jackson, and Apache
  Commons are not part of this boundary.
- `jdk-common.yml` contains summaries shared by JDK 8 and JDK 17.
- `jdk8.yml` contains JDK 8-specific summaries.
- `jdk17.yml` contains JDK 17 and JDK 11+ API summaries.

Schema stage:

- `summaries[].effects[].transfer` is supported.
- `noops` are supported for exact methods and package/class prefix selectors.
- Prefix selectors, for example `sun.*`, are allowed only in `noops`.
- Prefix selectors are rejected in transfer summaries.

Unsupported in this stage:

- `allocate` effects.
- `result[*]` factory or array effects.
- `container_summaries`.
