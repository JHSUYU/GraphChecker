# SOLR-18406: a follower's filecontent request for a generation its leader
# deleted after the reservation ran out (Solr 8.11).  Declarations only.
repo=/u/vnr3ne/lucene-solr-8_11
test_class=org.apache.solr.handler.TestCausynthPullReplicaReservation
test_method=pullReplicaFetchesAcrossALeaderCommit
target_occurrence=""
scope=(
  core:org/apache/solr/core/IndexDeletionPolicyWrapper
  core:org/apache/solr/handler/ReplicationHandler
  core:org/apache/solr/handler/IndexFetcher
  core:org/apache/solr/core/SolrDeletionPolicy
  lucene:org/apache/lucene/index/IndexFileDeleter
)
