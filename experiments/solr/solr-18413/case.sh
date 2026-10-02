# SOLR-18413: an update of a MIGRATE route key looks up a deleted target
# collection after the source leader applied it (Solr 8.11).  Declarations only.
repo=/bigtemp/vnr3ne/wt/lucene-solr-storing
test_class=org.apache.solr.cloud.TestCausynthMigrateRuleTarget
test_method=updateAfterRuleExpiryAndTargetDeletion
# The source leader's update of a!2, after the target's deletion: its
# routing rule had expired, so its path left at the expiry check before the
# target lookup: the leader's second update, a!1's being the first.
# The rule's expiry is the Overseer's clock (node0, the automatic cluster's
# first node); the source's leader, which checks it, is node1 (the tree's
# workload places it off the Overseer's node), so the skew is between nodes.
target_occurrence='auto0/node1#epoch0/region/REGION.f92dbcb6-b4d2-39a2-82db-2f935a7bd391#2'
scope=(
  core:org/apache/solr/update/processor/DistributedZkUpdateProcessor
  core:org/apache/solr/update/processor/DistributedUpdateProcessor
  core:org/apache/solr/cloud/api/collections/MigrateCmd
  core:org/apache/solr/cloud/overseer/SliceMutator
  solrj:org/apache/solr/common/cloud/RoutingRule
  solrj:org/apache/solr/common/cloud/ClusterState
  solrj:org/apache/solr/common/cloud/DocCollection
  solrj:org/apache/solr/common/cloud/Slice
)
