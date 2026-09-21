; Manual GraphChecker-style composition of a CLOSED report retry after deletion.
; AssignmentManager.java:1207-1217,1222-1234,1260-1302,1305-1315;
; DeleteTableProcedure.java:431-439; HRegionServer.java:2366-2423.
(set-logic QF_LIA)

; One modern CLOSE report is a WIRE family: accepted by the master, with
; exactly the same server, region, CLOSED transition, and nonnegative procId
; carried on retry. Only the first RPC response is lost to the RegionServer.
(declare-const originalProcId Int)
(declare-const retryProcId Int)
(declare-const sameReport Bool)
(declare-const firstAccepted Bool)
(declare-const ackLost Bool)
(declare-const retrySent Bool)
(assert (<= 0 originalProcId))
(assert (= retryProcId originalProcId))
(assert sameReport)
(assert firstAccepted)
(assert (= retrySent (and firstAccepted ackLost)))

; Event order and STATE family. This bounded scenario assumes no other
; operation removes or re-adds the region's RegionStateNode.
(declare-const firstReportTime Int)
(declare-const deleteTime Int)
(declare-const retryTime Int)
(declare-const firstRegionKnown Bool)
(declare-const deleteCompleted Bool)
(declare-const retryRegionKnown Bool)
(assert (<= 0 firstReportTime))
(assert (< firstReportTime retryTime))
(assert firstRegionKnown)
(assert deleteCompleted)
(assert (= retryRegionKnown (not (and deleteCompleted (< deleteTime retryTime)))))

; Master report path arms: online server and loaded meta pass the preceding
; gates. On a missing RegionStateNode, updateRegionTransition throws
; UnexpectedStateException before any remoteProc/id check. The public RPC
; catches IOException and returns response.errorMessage to the RS.
(declare-const reportingServerOnline Bool)
(declare-const metaLoaded Bool)
(assert reportingServerOnline)
(assert metaLoaded)
(define-fun unexpectedState () Bool
  (and retrySent reportingServerOnline metaLoaded (not retryRegionKnown)))
(define-fun errorResponse () Bool unexpectedState)

; Lost ACK, table deletion, then retry: named exception is reachable.
(push 1)
(assert ackLost)
(assert (< firstReportTime deleteTime))
(assert (< deleteTime retryTime))
(assert unexpectedState)
(check-sat)
(get-value (firstReportTime deleteTime retryTime retryRegionKnown unexpectedState errorResponse))
(pop 1)

; Retry before deletion: this particular missing-region guard cannot throw.
(push 1)
(assert ackLost)
(assert (< firstReportTime retryTime))
(assert (< retryTime deleteTime))
(assert unexpectedState)
(check-sat)
(pop 1)

; Delivered first ACK: the RegionServer has no reason to resend this report.
(push 1)
(assert (not ackLost))
(assert (< firstReportTime deleteTime))
(assert (< deleteTime retryTime))
(assert unexpectedState)
(check-sat)
(pop 1)
