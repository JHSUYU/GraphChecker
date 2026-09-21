# Metrics and logging production source reading (2026-09-19)

Read all 29 files under `hbase-logging/src/main` (3 Java files),
`hbase-metrics-api/src/main` (15 Java files), and `hbase-metrics/src/main`
(10 Java files and one `META-INF/services` resource) in full. Before marking
them `full` in `hbase-main-reading-index.tsv`, checked every file's current
SHA-256 and physical line count against the index. The index now records
86 of 3,289 production files as fully read.

## Coordination relationships examined

- Logging setup bridges JUL to SLF4J and reaches into the Log4j context to
  control file appenders and logger levels. The active-context and appender
  branches are local logging configuration, with no demonstrated distributed
  coordination state leading to a requested exception target.
- `MetricRegistriesLoader` selects a `MetricRegistries` implementation via
  `ServiceLoader`; the implementation resource points at
  `MetricRegistriesImpl`. `MetricRegistriesImpl` uses `RefCountingMap` to share
  registries by `MetricRegistryInfo`. The map's compute operations maintain a
  reference count across create/remove calls; this is process-local lifetime
  coordination, but no qualifying branch-triggered exception was found.
- `MetricRegistryImpl` lazily obtains counters, gauges, histograms, meters,
  and timers; `FastLongHistogram` uses bounded buckets and a snapshot/reset
  path. These classes report observations rather than authorize a distributed
  control-plane decision. No finding was counted from this module pass.

The metric timer's unit conversion and `MetricRegistryInfo` equality deserve
ordinary correctness review but do not satisfy this investigation's
coordination/explicit-exception criterion, so they were excluded.
