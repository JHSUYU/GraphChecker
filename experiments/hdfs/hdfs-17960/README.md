# HDFS-17960

This experiment runs the standard GraphChecker stages on the Java 8 Hadoop
checkout at `/tmp/hdfs-17960-vulnerable`. The workload is
`TestOrderedSnapshotDeletion.testOrderedDeletionWithRestart`; its checkpoint
reaches the annotated snapshot-count consistency check.

`run.sh prepare` builds the independent checkout and records the expected
workload failure. `run.sh tasks` performs static analysis, both runtime trace
passes, and target-first scheduling with the generic LLM symbolic-input
selector. `run.sh candidates` performs concolic replay, symbolic merging, SMT
composition, and Z3 evaluation using the same pipeline as HDFS-11741.
