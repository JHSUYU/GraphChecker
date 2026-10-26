repo=${GC_TREES}/solr-bug-6101
test_class=org.apache.solr.cloud.TestCausynthSplitShardLegacy
test_method=splitUnderLegacyCloud
target_occurrence='auto0/node0#epoch0/region/REGION.05d95c18-e743-3177-861c-d3167f8ea67b#2'
scope=(
  core:org/apache/solr/core/CoreContainer
  core:org/apache/solr/cloud/api/collections/SplitShardCmd
  core=:org/apache/solr/cloud/Overseer
  core:org/apache/solr/cloud/api/collections/CreateCollectionCmd
  core:org/apache/solr/cloud/api/collections/AddReplicaCmd
  core:org/apache/solr/cloud/overseer/ReplicaMutator
  core=:org/apache/solr/cloud/ZkController
)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
