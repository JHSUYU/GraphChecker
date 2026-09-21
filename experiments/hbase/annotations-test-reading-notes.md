# hbase-annotations test-tree reading

Read all 22 files under `hbase/hbase-annotations/src/test` in full on 2026-09-19 (812 Java lines; no non-Java files). All are interfaces in `org.apache.hadoop.hbase.testclassification` that expose one `TAG` string for JUnit test classification. Their comments describe categories or duration expectations; none contains a test method, an executable branch, an exception throw, or distributed coordination state. Thus there is no strict coordination-state if→throw candidate in this module's test tree. This is a complete source read, not an inference from filenames. No shared index or ledger was modified.

| File (all under `testclassification/`) | Lines | SHA-256 | Actual content / workload role |
| --- | ---: | --- | --- |
| `ClientTests.java` | 40 | `055a145e76ea2a64d46272c690adc8e97c1aaf80c5dc3ff631a093e7b3f7fe28` | Client-related category, including hbase-client and server client tests; constant only. |
| `CoprocessorTests.java` | 39 | `23950a5af97c815ee6df3a95b18017688540eba660c8396bddfab208f9c5f4df` | Coprocessor category; constant only. |
| `FilterTests.java` | 39 | `911282ef716f7965ec44f25df3ef4af87397be88ecdd80b46b0d2a00592b981e` | HBase filter package category; constant only. |
| `FlakeyTests.java` | 39 | `bdc6326b63f1e14c69fa7498a30172a26158690944383d02eaf5402ebda99c7d` | Tests that commonly fail on public build infrastructure; constant only. |
| `IOTests.java` | 40 | `6ba45669753dc53fa0d2de8b8221efaacb5c7372e05358760b70623feea93128` | HBase IO/HFile category; constant only. |
| `IntegrationTests.java` | 38 | `28f0e3a8c01d3f2018039b48ddaedd6d0360390e9e55f20a86f470aa052e12ce` | Documents long-running, mini or real cluster tests, possible cluster mutation, and no parallel integration tests; constant only. |
| `LargeTests.java` | 37 | `c6df7705d974f0be09cb88dd21b071bf60211ffdf6cc4f0ed85fff399128a39d` | Documents isolated JVM and about three-minute target/ten-minute limit; constant only. |
| `MapReduceTests.java` | 39 | `8802da4b9867ca26e8818987759c58e0ce477fb747938ff9c8c899a24175ae7b` | MapReduce-related category; constant only. |
| `MasterTests.java` | 39 | `b0f87485929b26b7f98b815da14b6a0acd79b5a653e8b2a9419afa42c23bf103` | Master-related category; constant only. |
| `MediumTests.java` | 36 | `aafbb055fb22e6340f8fcdcc88a992eb50f4c35991e2c8124c3f061064f36c09` | Documents isolated JVM, approximate 50-second target, and cluster-needed use; constant only. |
| `MetricsTests.java` | 25 | `24526fe9523bfbf0e3928ebdda2cc2632ca4cf5b37e846ea93d29487e6b11fbf` | Metrics category; constant only. |
| `MiscTests.java` | 39 | `d8225a612e677dd886a39486d655529a2e2f34d9b1106b60729bc45f419f1d55` | Uncategorized miscellaneous tests; constant only. |
| `RPCTests.java` | 39 | `6e600085d67fa4dfe51cd27563fc55589a3a3d4dca9bbc18b3409a25e8ac67e6` | RPC-related category; constant only. |
| `RSGroupTests.java` | 25 | `af1b2c1f582b5df5e751bc40fc7179f44b0647987934e546892f57877a216aac` | RegionServer group feature category; constant only. |
| `RegionServerTests.java` | 39 | `c068056352f36db5c1d577d1bd5eaa4d3fde43cdca2e72d12983192101ad040e` | RegionServer-related category; constant only. |
| `ReplicationTests.java` | 39 | `98c7a0dfb3fced543fcdf8d1869bcd8d1f93fc4274e40c6f3df2ed789bb44925` | Replication-related category; constant only. |
| `RestTests.java` | 39 | `32351a664dbf31a91f2423e53d0d72503e862a00e3d0a3092dd2c56f4f8d93f9` | HBase REST category; constant only. |
| `SecurityTests.java` | 39 | `c2cc245c0cc22ec1e7a18f02128d8af75941cb1721f55e36b64bc9a5c79183dc` | Security-related category; constant only. |
| `SmallTests.java` | 34 | `e6c68838bbaaacf5e8d4cd451105afe8d653990bcfd12a7034f7648f129896b0` | Documents shared JVM, under-15-second target, and no-cluster requirement; constant only. |
| `VerySlowMapReduceTests.java` | 41 | `77fbb13bc8c1f12ec61bbaabb13748838272c144ab99e69c4578eb7619b1e6ea` | MapReduce tests taking over five minutes on public CI; constant only. |
| `VerySlowRegionServerTests.java` | 41 | `272eb4598f42c8d7e99b131227a60e9aea283132cb358d94cf7d054cbcbd22c6` | RegionServer tests taking over five minutes on public CI; constant only. |
| `ZKTests.java` | 26 | `f877320e5226b4723536ef744020b73a1c0a91891aaf748943f89f4aac5258e6` | ZooKeeper tool-logic tests (example `RecoverableZooKeeper`), explicitly distinct from all tests merely depending on ZooKeeper; constant only. |
