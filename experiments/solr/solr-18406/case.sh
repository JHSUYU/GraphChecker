# SOLR-18406: a follower's filecontent request for a generation its leader
# deleted after the reservation ran out (Solr 8.11).  Declarations only.
repo=/u/vnr3ne/lucene-solr-8_11
test_class=org.apache.solr.handler.TestCausynthPullReplicaReservation
test_method=pullReplicaFetchesAcrossALeaderCommit
# The leader's first filecontent of G, the first after the commit of G+1
# the leader made while the follower held filelist(G).
target_occurrence='auto0/node0#epoch0/region/REGION.fdbd628a-263b-3ec0-abef-a6e7f5ee70f6/ctx:Anchor:5210ec5472ea1b39@SOLR_HTTP/.replication/idx:<org.apache.solr.handler.ReplicationHandler$DirectoryFileStream: void write(java.io.OutputStream)>@0/<org.apache.solr.handler.ReplicationHandler$DirectoryFileStream: void initWrite()>@0'
scope=(
  core:org/apache/solr/core/IndexDeletionPolicyWrapper
  core:org/apache/solr/handler/ReplicationHandler
  core:org/apache/solr/handler/IndexFetcher
  core:org/apache/solr/core/SolrDeletionPolicy
  lucene:org/apache/lucene/index/IndexFileDeleter
)
