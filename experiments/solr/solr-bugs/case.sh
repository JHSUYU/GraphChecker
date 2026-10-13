# Solr 8.11 coordination bugs of the bug study (the owner's reports 5-10 of
# 2026-10-08, docs/checks/VERIFIED-BUGS.md) on the tree gc/solr-checks (the
# fork's graphchecker/solr-checks), which marks each case's target throw with
# @CausynthExceptionTarget("solr-bugs-<case>") and holds its workload, a
# MiniSolrCloudCluster test of its own (TestCausynth*: no test of the tree
# takes the path without failing).  Each workload passes natively: its
# recording takes the path without the failure, and the witness is the
# engine's (a fault, a clock, a re-paired read).  Declarations only.
#
# A case whose target throw runs more than once in its window (a second
# MIGRATE's buffer request, every routed add, every client request) declares
# the occurrence its bug is about by a selector; until the selector is read
# off a recording (the discovery hook, experiments/lib/README), it declares
# none, and PLAN refuses the run and lists the observed occurrences.
repo=${GC_TREES}/lucene-solr-checks
case "${1:?usage: case.sh <bug>}" in
  # Bug study #04: a reindex's abort cleans up by deleting its target T,
  # which an alias still names; DELETE refuses it and the source S stays
  # read-only.  The workload holds the reindex once S is read-only and T
  # exists, aliases A to T, removes A (a failure is logged, not fatal),
  # aborts, and adds to S after the cleanup.  The witness: a fault on the
  # DELETEALIAS request (the report's trigger was a concurrent CREATEALIAS,
  # whose order against the cleanup the workload's own requests fix).  The
  # target: the cleanup's DELETE of T, the window's first DELETE.
  reindex-cleanup)
    test_class=org.apache.solr.cloud.TestCausynthReindexAbortAlias
    test_method=abortAfterAnAliasOfTheTargetIsRemoved
    target_occurrence=first
    scope=(
      core:org/apache/solr/cloud/api/collections/DeleteCollectionCmd
      core:org/apache/solr/cloud/api/collections/ReindexCollectionCmd
      core:org/apache/solr/cloud/api/collections/DeleteAliasCmd
      core:org/apache/solr/cloud/api/collections/OverseerCollectionMessageHandler
      solrj:org/apache/solr/common/cloud/Aliases
      solrj:org/apache/solr/common/cloud/ZkStateReader)
    ;;
  # Bug study #17: MIGRATE has the target leader buffer updates first and
  # applies them only at its end; a failure between leaves the target
  # BUFFERING, and the next MIGRATE into it is refused at its buffer request.
  # The workload migrates two keys into one target; the witness, a fault at
  # a door of the first MIGRATE after its buffer request.  The target: the
  # second MIGRATE's buffer request, the second occurrence of the buffer
  # lambda on the target's node (round SG1's recording: Overseer tasks #3
  # and #4).
  migrate-buffer-leak)
    test_class=org.apache.solr.cloud.TestCausynthMigrateBufferLeak
    test_method=twoMigratesIntoOneTarget
    target_occurrence='auto0/node1#epoch0/region/REGION.f524143b-7e54-33b5-b7b7-75fdecf194e7#2'
    scope=(
      core:org/apache/solr/cloud/api/collections/MigrateCmd
      core:org/apache/solr/handler/admin/CoreAdminOperation
      core:org/apache/solr/update/UpdateLog
      core:org/apache/solr/cloud/api/collections/OverseerCollectionMessageHandler)
    ;;
  # Bug study #50: the Overseer takes a collection's lock for a task, then
  # writes its async id to the running map; only NodeExists or an interrupt
  # gives the lock back, so a ZooKeeper OperationTimeout there leaks it and
  # the task never runs.  The workload turns a collection read-only, turns it
  # back with an asynchronous request, waits a bounded number of status
  # requests, and adds.  The witness: that fault on the running-map write.
  # The target: the add's read-only refusal, the window's first add.
  overseer-lock-leak)
    test_class=org.apache.solr.cloud.TestCausynthOverseerLockLeak
    test_method=addAfterAnAsyncReadOnlyOff
    target_occurrence=first
    scope=(
      core:org/apache/solr/cloud/OverseerTaskProcessor
      core:org/apache/solr/cloud/LockTree
      core:org/apache/solr/cloud/DistributedMap
      core:org/apache/solr/cloud/api/collections/OverseerCollectionMessageHandler
      core:org/apache/solr/update/processor/DistributedZkUpdateProcessor
      solrj:org/apache/solr/common/cloud/SolrZkClient)
    ;;
  # Bug study #16: CREATESNAPSHOT asks only the replicas its Overseer sees
  # ACTIVE and records success while no request it sent failed.  The workload
  # creates the shard's leader on the Overseer's node, adds a replica on the
  # other node (no final state awaited; the client waits for it ACTIVE in its
  # own view), snapshots the shard, deletes the leader replica, and backs up
  # from the snapshot (non-incremental, the path that reads it).  The
  # witness: the Overseer's view of the added replica not ACTIVE yet at
  # CREATESNAPSHOT.  The target: the backup's search for a live replica with
  # the snapshot, the window's only one.  The chain starts at the Overseer's
  # view of a replica's state, which Replica.<init> derives from the decoded
  # leaf: outside every region it runs with no VM model, and
  # CreateSnapshotCmd's ACTIVE test decided concretely in every occurrence
  # (SGF, 168 of 168).  The scope holds the classes that build the view, as
  # solr-18413's: with them the node's watch callback is a region and the
  # decode runs in it; Replica alone, Slice with it or ClusterState with it
  # root no region the decode runs (rounds Z3A, Z3B, Z3C).  Their lookup and
  # construction paths took round 1 from 2 obligations to 3384 over 101
  # (site, ordinal, arm) triples (round Z2T), so flips are asked from the
  # seed's paths only (world depth 0, named BOUNDED): the bug's mechanism is
  # one flip there, a pairing of the Overseer's view at CREATESNAPSHOT with
  # an older decode of state.json (round Z3D: round 1 198 obligations).
  snapshot-no-active)
    test_class=org.apache.solr.cloud.TestCausynthSnapshotBackup
    test_method=backupFromASnapshotAfterItsLeaderIsGone
    target_occurrence=first
    scope=(
      core:org/apache/solr/cloud/api/collections/CreateSnapshotCmd
      core:org/apache/solr/cloud/api/collections/BackupCmd
      core:org/apache/solr/core/snapshots/SolrSnapshotManager
      core:org/apache/solr/core/snapshots/CollectionSnapshotMetaData
      solrj:org/apache/solr/common/cloud/ZkStateReader
      solrj:org/apache/solr/common/cloud/ClusterState
      solrj:org/apache/solr/common/cloud/DocCollection
      solrj:org/apache/solr/common/cloud/Slice
      solrj:org/apache/solr/common/cloud/Replica)
    export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
    ;;
  # Bug study #26: a RESTORE into a new collection marks its shards
  # CONSTRUCTION and ACTIVE only at its end; a retry into the collection it
  # left restores the cores and never marks them, so no update finds an
  # active shard.  The workload restores one backup twice into one
  # collection and adds to it; the witness, a fault at the first RESTORE's
  # RESTORECORE or buffered-updates request.  The target: the add's routing
  # after the second RESTORE, the client's third routed update (round SG1's
  # recording: the source's two adds, then the add to the target).
  restore-construction)
    test_class=org.apache.solr.cloud.TestCausynthRestoreRetry
    test_method=restoreTwiceThenAdd
    target_occurrence='auto0/client0#epoch0/region/REGION.9c74b1fc-0155-3e44-b37f-0634809064c9#3'
    scope=(
      core:org/apache/solr/cloud/api/collections/RestoreCmd
      solrj:org/apache/solr/common/cloud/HashBasedRouter
      solrj:org/apache/solr/common/cloud/Slice)
    ;;
  # Bug study #20: a time routed alias's first document fixes the start its
  # date math names by writing the routing node's captured view of every
  # alias back, over a newer alias.  The workload creates the plain alias B
  # before the routed alias's first document and requests via B after the
  # start is rewritten.  The witness: the routing node's view captured before
  # B.  The target: the client's lookup of B, the request via B: the sixth
  # occurrence of the client's request region in round SG1's recording
  # (CREATE, two CREATEALIASes, two updates, then the query, .select#1).
  tra-start-overwrite)
    test_class=org.apache.solr.cloud.TestCausynthTraStartAlias
    test_method=requestViaAnAliasCreatedBeforeTheFirstDocument
    target_occurrence='auto0/client0#epoch0/region/REGION.d05f0711-30a1-3795-816a-5d70c9e38216#6'
    scope=(
      core:org/apache/solr/cloud/api/collections/TimeRoutedAlias
      solrj:org/apache/solr/common/cloud/ZkStateReader
      solrj:org/apache/solr/common/cloud/Aliases
      solrj:org/apache/solr/client/solrj/impl/BaseCloudSolrClient)
    ;;
  *)
    echo "unknown Solr bug-study case: $1" >&2
    return 2
    ;;
esac
