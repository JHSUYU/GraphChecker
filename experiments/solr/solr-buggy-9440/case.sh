repo=${GC_TREES}/solr-bug-9440
test_class=org.apache.solr.cloud.TestCausynthForceLeaderStaleView
test_method=forceLeaderOnAWatchingNode
target_occurrence=first
scope=(
  core:org/apache/solr/handler/admin/CollectionsHandler
)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
