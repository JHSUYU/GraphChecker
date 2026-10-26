repo=${GC_TREES}/solr-bug-6197
test_class=org.apache.solr.cloud.TestCausynthMigrateLegacy
test_method=migrateUnderLegacyCloud
target_occurrence=first
scope=(
  core:org/apache/solr/core/CoreContainer
  core:org/apache/solr/cloud/api/collections/MigrateCmd
)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
