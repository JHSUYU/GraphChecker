# SOLR-18413: an update of a MIGRATE route key looks up a deleted target
# collection after the source leader applied it (Solr 8.11).  Declarations only.
repo=/u/vnr3ne/lucene-solr-8_11
test_class=org.apache.solr.cloud.TestCausynthMigrateRuleTarget
test_method=updateAfterRuleExpiryAndTargetDeletion
target_occurrence=""
scope=(
  core:org/apache/solr/update/processor/DistributedZkUpdateProcessor
  core:org/apache/solr/update/processor/DistributedUpdateProcessor
  core:org/apache/solr/cloud/api/collections/MigrateCmd
  solrj:org/apache/solr/common/cloud/RoutingRule
  solrj:org/apache/solr/common/cloud/ClusterState
  solrj:org/apache/solr/common/cloud/DocCollection
  solrj:org/apache/solr/common/cloud/Slice
)
