repo=${GC_TREES}/hbase-checks
case "${1:?usage: case.sh <bug>}" in
  master-active-time)
    test_class=org.apache.hadoop.hbase.master.procedure.TestSplitWALProcedure
    test_method=testMasterRestart
    target_occurrence=first
    recording_window=startup
    scope=(
      server:org/apache/hadoop/hbase/master/MasterRpcServices
      server=:org/apache/hadoop/hbase/master/HMaster
      server:org/apache/hadoop/hbase/master/procedure/RSProcedureDispatcher
      server:org/apache/hadoop/hbase/master/procedure/SplitWALRemoteProcedure
      procedure:org/apache/hadoop/hbase/procedure2/RemoteProcedureDispatcher
      server=:org/apache/hadoop/hbase/regionserver/RSRpcServices
      server=:org/apache/hadoop/hbase/regionserver/HRegionServer
      server:org/apache/hadoop/hbase/regionserver/RemoteProcedureResultReporter
      server:org/apache/hadoop/hbase/regionserver/handler/RSProcedureHandler
      common=:org/apache/hadoop/hbase/util/EnvironmentEdgeManager
      common:org/apache/hadoop/hbase/util/DefaultEnvironmentEdge)
    ;;
  *)
    echo "unknown HBase bug-study case: $1" >&2
    return 2
    ;;
esac
