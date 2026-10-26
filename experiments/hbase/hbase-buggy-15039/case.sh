repo=${GC_TREES}/hbase-bug-15039
test_class=org.apache.hadoop.hbase.security.token.TestCausynthTokenKeyWatch
test_method=theOtherServerValidatesATokenOfANewKey
target_occurrence=first
scope=(
  server=:org/apache/hadoop/hbase/security/token/AuthenticationTokenSecretManager
  server=:org/apache/hadoop/hbase/security/token/ZKSecretWatcher)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
