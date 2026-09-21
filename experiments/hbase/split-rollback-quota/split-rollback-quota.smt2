; HBASE-SPLIT-ROLLBACK-QUOTA-001
; SplitTableRegionProcedure PRE_OPERATION increments NamespaceStateManager's
; cached count. A later rollback removes daughters but has no compensating decrement.
(set-logic QF_LIA)
(declare-const actual_regions_before Int)
(declare-const quota_max Int)
(declare-const cached_regions_after_reservation Int)
(declare-const first_split_rolls_back Bool)
(declare-const rollback_releases_reservation Bool)
(declare-const actual_regions_after_rollback Int)
(declare-const cached_regions_after_rollback Int)
(declare-const second_split_throws Bool)

(assert (= actual_regions_before 1))
(assert (= quota_max 2))
(assert (= cached_regions_after_reservation (+ actual_regions_before 1)))
(assert first_split_rolls_back)
(assert (= actual_regions_after_rollback actual_regions_before))
(assert (= cached_regions_after_rollback
  (ite rollback_releases_reservation
    (- cached_regions_after_reservation 1)
    cached_regions_after_reservation)))
; NamespaceStateManager.checkAndUpdateNamespaceRegionCount rejects incr=1
; when the cached count is already at the namespace maximum.
(assert (= second_split_throws (>= cached_regions_after_rollback quota_max)))

(push)
(assert (not rollback_releases_reservation))
(assert (< actual_regions_after_rollback quota_max))
(assert second_split_throws)
(check-sat)
(pop)

(push)
(assert rollback_releases_reservation)
(assert second_split_throws)
(check-sat)
(pop)
