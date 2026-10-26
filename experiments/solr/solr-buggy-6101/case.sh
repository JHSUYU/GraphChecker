repo=${GC_TREES}/solr-bug-6101
test_class=org.apache.solr.cloud.TestCausynthSplitShardLegacy
test_method=splitUnderLegacyCloud
target_occurrence=first
scope=(
  core:org/apache/solr/core/CoreContainer
  core=:org/apache/solr/cloud/Overseer
  core:org/apache/solr/cloud/api/collections/SplitShardCmd
)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
