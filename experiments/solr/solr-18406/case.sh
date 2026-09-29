# SOLR-18406: a follower's filecontent request for a generation its leader
# deleted after the reservation ran out (Solr 8.11).  Declarations only.
repo=/u/vnr3ne/lucene-solr-8_11
test_class=org.apache.solr.cloud.TestCausynthPullReplicaReservation
test_method=pullReplicaFetchesWhileLeaderCommits
# The leader's 66th filecontent, the first of generation G after a commit
# that asked the deletion policy to delete G mid-fetch (the recording's third
# poll): only G's reservation kept it.
target_occurrence="auto0/node0#epoch0/region/REGION.fdbd628a-263b-3ec0-abef-a6e7f5ee70f6/ctx:Anchor:8bb5d0f59d5e075f@SOLR_HTTP/REPLICATION_POLL/idx:<org.apache.solr.handler.ReplicationHandler$DirectoryFileStream: void write(java.io.OutputStream)>@0/<org.apache.solr.handler.ReplicationHandler$DirectoryFileStream: void initWrite()>@0"
scope=(
  core:org/apache/solr/core/IndexDeletionPolicyWrapper
  core:org/apache/solr/handler/ReplicationHandler
  core:org/apache/solr/handler/IndexFetcher
  core:org/apache/solr/core/SolrDeletionPolicy
  lucene:org/apache/lucene/index/IndexFileDeleter
)
