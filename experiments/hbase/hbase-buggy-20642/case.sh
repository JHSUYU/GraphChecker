repo=${GC_TREES}/hbase-bug-20642
test_class=org.apache.hadoop.hbase.master.procedure.TestCausynthDisableRetryNonce
test_method=disableTwoTables
target_occurrence='auto0/master0#epoch0/region/REGION.98cba534-e757-3508-990f-4855688e1e1e#2'
scope=(
  server=:org/apache/hadoop/hbase/master/procedure/AbstractStateMachineTableProcedure
  server=:org/apache/hadoop/hbase/master/TableStateManager)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=1
