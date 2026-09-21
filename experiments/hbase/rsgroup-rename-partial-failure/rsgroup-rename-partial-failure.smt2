; HBASE-RSGROUP-RENAME-PARTIAL-FAILURE-001
; RSGroupInfoManagerImpl.renameRSGroup first commits the group map in flushConfig,
; then invokes setRSGroup to modify the affected table descriptors.
(set-logic QF_UF)
(declare-const flush_config_succeeded Bool)
(declare-const descriptor_update_failed Bool)
(declare-const old_group_present_after_first_call Bool)
(declare-const new_group_present_after_first_call Bool)
(declare-const table_still_references_old_group Bool)
(declare-const first_call_fails Bool)
(declare-const client_retries_old_to_new Bool)
(declare-const retry_throws_constraint Bool)

(assert flush_config_succeeded)
(assert (= old_group_present_after_first_call (not flush_config_succeeded)))
(assert (= new_group_present_after_first_call flush_config_succeeded))
(assert (= table_still_references_old_group descriptor_update_failed))
(assert (= first_call_fails descriptor_update_failed))
(assert (= client_retries_old_to_new first_call_fails))
; getRSGroupInfo(oldName) checks the newly published group map on retry.
(assert (= retry_throws_constraint
  (and client_retries_old_to_new (not old_group_present_after_first_call))))

(push)
(assert descriptor_update_failed)
(assert table_still_references_old_group)
(assert new_group_present_after_first_call)
(assert retry_throws_constraint)
(check-sat)
(pop)

; If the descriptor update succeeds, the retry/target exception is unreachable.
(push)
(assert (not descriptor_update_failed))
(assert retry_throws_constraint)
(check-sat)
(pop)
