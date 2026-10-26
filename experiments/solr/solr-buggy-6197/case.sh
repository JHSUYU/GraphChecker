repo=${GC_TREES}/solr-bug-6197
test_class=org.apache.solr.cloud.TestCausynthMigrateLegacy
test_method=migrateUnderLegacyCloud
target_occurrence='auto0/node1#epoch0/region/REGION.05d95c18-e743-3177-861c-d3167f8ea67b#2'
scope=(
  core:org/apache/solr/core/CoreContainer
  core:org/apache/solr/cloud/api/collections/MigrateCmd
  core=:org/apache/solr/cloud/CausynthLegacyCloud
)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
