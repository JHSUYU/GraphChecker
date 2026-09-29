# SOLR-18406: a follower's filecontent request for a generation its leader
# deleted after the reservation ran out (Solr 8.11).  Declarations only.
repo=/u/vnr3ne/lucene-solr-18406
test_class=org.apache.solr.handler.TestCausynthPullReplicaReservation
test_method=pullReplicaFetchesAcrossALeaderCommit
# The leader's first filecontent of G, the first after the commit of G+1
# the leader made while the follower held filelist(G): the follower fetches
# nothing before the hold, so it is the leader's first filecontent.
target_occurrence=first
scope=(
  core:org/apache/solr/core/IndexDeletionPolicyWrapper
  core:org/apache/solr/handler/ReplicationHandler
  core:org/apache/solr/handler/IndexFetcher
  core:org/apache/solr/core/SolrDeletionPolicy
  lucene:org/apache/lucene/index/IndexFileDeleter
)
