; HBASE-RSGROUP-RENAME-NAMESPACE-001
; A successful RSGroup rename changes the group map and table descriptors,
; but does not update namespace descriptors that name the old group.
(set-logic QF_UF)
(declare-const rename_committed Bool)
(declare-const namespace_referenced_old_before Bool)
(declare-const namespace_reference_updated Bool)
(declare-const old_group_exists_after Bool)
(declare-const new_group_exists_after Bool)
(declare-const new_table_uses_namespace_group Bool)
(declare-const inherited_group_exists Bool)
(declare-const create_table_throws_constraint Bool)

(assert rename_committed)
(assert namespace_referenced_old_before)
(assert new_table_uses_namespace_group)
(assert (= old_group_exists_after (not rename_committed)))
(assert (= new_group_exists_after rename_committed))
(assert (= inherited_group_exists
  (ite namespace_reference_updated new_group_exists_after old_group_exists_after)))
(assert (= create_table_throws_constraint
  (and new_table_uses_namespace_group (not inherited_group_exists))))

(push)
(assert (not namespace_reference_updated))
(assert create_table_throws_constraint)
(check-sat)
(pop)

; Updating the namespace descriptor to the new name removes this failure.
(push)
(assert namespace_reference_updated)
(assert create_table_throws_constraint)
(check-sat)
(pop)
