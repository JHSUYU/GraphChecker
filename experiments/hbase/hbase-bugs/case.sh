repo=${GC_TREES}/hbase-checks
case "${1:?usage: case.sh <bug>}" in
  master-active-time)
    test_class=org.apache.hadoop.hbase.master.assignment.TestCausynthMasterActiveTime
    test_method=reportOpenedToTheNextMaster
    target_occurrence='auto0/master1#epoch0/region/REGION.f3a7cc84-4aa9-3e73-ae53-0232639dea95#1'
    recording_window=startup
    scope=(
      server:org/apache/hadoop/hbase/master/MasterRpcServices
      server=:org/apache/hadoop/hbase/master/HMaster
      server=:org/apache/hadoop/hbase/master/assignment/OpenRegionProcedure
      server=:org/apache/hadoop/hbase/master/assignment/RegionRemoteProcedureBase
      server:org/apache/hadoop/hbase/master/procedure/RSProcedureDispatcher
      procedure:org/apache/hadoop/hbase/procedure2/RemoteProcedureDispatcher
      server=:org/apache/hadoop/hbase/regionserver/RSRpcServices
      server=:org/apache/hadoop/hbase/regionserver/HRegionServer
      server=:org/apache/hadoop/hbase/regionserver/handler/AssignRegionHandler
      server=:org/apache/hadoop/hbase/regionserver/RegionServerServices
      common=:org/apache/hadoop/hbase/util/EnvironmentEdgeManager
      common:org/apache/hadoop/hbase/util/DefaultEnvironmentEdge)
    ;;
  backup-lock-reply-lost)
    test_class=org.apache.hadoop.hbase.backup.TestCausynthBackupLockReplyLost
    test_method=takeAndReleaseTheBackupLock
    target_occurrence=first
    scope=(
      backup=:org/apache/hadoop/hbase/backup/impl/BackupSystemTable
      backup=:org/apache/hadoop/hbase/backup/impl/BackupManager)
    ;;
  ns-rsgroup-removal)
    test_class=org.apache.hadoop.hbase.rsgroup.TestCausynthNamespaceGroupRemoval
    test_method=removeTheGroupOfANamespaceBeingCreated
    target_occurrence='auto0/master0#epoch0/region/REGION.874dbcb2-c79c-38ee-bb4f-4dfdf62bd234#3'
    scope=(
      server=:org/apache/hadoop/hbase/master/procedure/MasterProcedureUtil
      server=:org/apache/hadoop/hbase/rsgroup/RSGroupInfoManagerImpl
      server=:org/apache/hadoop/hbase/master/TableNamespaceManager
      server=:org/apache/hadoop/hbase/master/ClusterSchemaServiceImpl)
    ;;
  *)
    echo "unknown HBase bug-study case: $1" >&2
    return 2
    ;;
esac
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
