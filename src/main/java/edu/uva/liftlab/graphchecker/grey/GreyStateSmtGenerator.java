package edu.uva.liftlab.graphchecker.grey;

public final class GreyStateSmtGenerator {
    public String generate(GreyStateSpec spec, GreyStateAnalysisResult result) {
        int k = spec.getBound();
        boolean hasValidation = hasEvent(result, "VALIDATE_MAP_LOOKUP");
        boolean hasRemoval = hasEvent(result, "MAP_REMOVE");
        boolean hasSend = hasEvent(result, "SEND_METADATA");
        boolean hasReceive = hasEvent(result, "RECEIVE_METADATA");
        boolean hasNoRepair = hasEvent(result, "RECOVERY_NO_REPAIR");
        boolean hasRepair = hasEvent(result, "RECOVERY_CLEAR_OR_RETRY");
        boolean balancerRefreshesOnExpiry = hasEventInMethod(result,
                "CACHE_REFRESH_ON_EXPIRY", "org.apache.hadoop.hdfs.server.balancer.KeyManager")
                || hasEventInMethod(result,
                "CACHE_REFRESH_ON_VALIDITY_GUARD", "org.apache.hadoop.hdfs.server.balancer.KeyManager");
        boolean balancerReusesWithoutExpiryCheck = hasEventInMethod(result,
                "CACHE_REUSE_WITHOUT_EXPIRY_CHECK", "org.apache.hadoop.hdfs.server.balancer.KeyManager");
        boolean refreshesOnExpiry = balancerRefreshesOnExpiry
                || (!balancerReusesWithoutExpiryCheck
                && (hasEvent(result, "CACHE_REFRESH_ON_EXPIRY")
                || hasEvent(result, "CACHE_REFRESH_ON_VALIDITY_GUARD")));
        boolean reusesWithoutExpiryCheck = balancerReusesWithoutExpiryCheck
                || (!refreshesOnExpiry && hasEvent(result, "CACHE_REUSE_WITHOUT_EXPIRY_CHECK"));
        StringBuilder out = new StringBuilder();
        out.append("; Auto-generated bounded grey-state lifecycle model\n");
        out.append("; This is an abstract model generated from semantic summaries.\n\n");
        out.append("(set-logic AUFLIA)\n");
        out.append("(declare-sort DEK 0)\n");
        out.append("(declare-fun dekKeyId (DEK) Int)\n");
        out.append("(declare-fun dekExpiry (DEK) Int)\n");
        out.append("(declare-const nullDEK DEK)\n\n");
        out.append("(declare-fun hasKey (Int Int) Bool) ; round,keyId -> present in validator map\n");
        out.append("(declare-fun keyExpiry (Int) Int)\n");
        out.append("(declare-fun cachedDEK (Int) DEK)\n");
        out.append("(declare-fun time (Int) Int)\n");
        out.append("(declare-fun send (Int) Bool)\n");
        out.append("(declare-fun receive (Int) Bool)\n");
        out.append("(declare-fun validate (Int) Bool)\n");
        out.append("(declare-fun noEffectiveRecovery (Int) Bool)\n");
        out.append("(declare-fun staleCachedDEK (Int) Bool)\n\n");
        for (int i = 0; i < k; i++) {
            out.append("(assert (<= (time ").append(i).append(") (time ").append(i + 1).append(")))\n");
        }
        out.append("\n");
        out.append("; Abstract expiration/removal relation for keys relevant to the fatal predicate.\n");
        out.append("; A later round may lack a key whose expiry is before the local time.\n");
        if (hasRemoval) {
            for (int i = 0; i <= k; i++) {
                out.append("(assert (forall ((K Int)) ")
                        .append("(=> (< (keyExpiry K) (time ").append(i).append(")) ")
                        .append("(not (hasKey ").append(i).append(" K)))))\n");
            }
        } else {
            out.append("; MAP_REMOVE was not extracted; key disappearance is left unconstrained.\n");
        }
        out.append("\n");
        if (refreshesOnExpiry) {
            out.append("; Relevant cache summary includes expiry refresh. Sending stale cached DEK is disallowed.\n");
            for (int i = 0; i <= k; i++) {
                out.append("(assert (=> (send ").append(i).append(") ")
                        .append("(not (staleCachedDEK ").append(i).append("))))\n");
                out.append("(assert (=> (not (staleCachedDEK ").append(i).append(")) ")
                        .append("(hasKey ").append(i).append(" (dekKeyId (cachedDEK ").append(i).append(")))))\n");
            }
        } else if (reusesWithoutExpiryCheck) {
            out.append("; Relevant cache summary lacks expiry refresh, so stale cached DEK is possible.\n");
            out.append("(assert (exists ((R Int)) (and (>= R 0) (<= R ").append(k)
                    .append(") (staleCachedDEK R))))\n");
        } else {
            out.append("; No cache summary was extracted; stale cached metadata remains symbolic.\n");
        }
        out.append("\n");
        if (hasRepair && !hasNoRepair) {
            out.append("; Extracted recovery clears/retries metadata and no no-repair path was found.\n");
            for (int i = 0; i <= k; i++) {
                out.append("(assert (not (noEffectiveRecovery ").append(i).append(")))\n");
            }
        } else if (hasNoRepair) {
            out.append("; At least one path lacks effective recovery.\n");
            out.append("(assert (exists ((R Int)) (and (>= R 0) (<= R ").append(k)
                    .append(") (noEffectiveRecovery R))))\n");
        } else {
            out.append("; Recovery was not classified; noEffectiveRecovery remains symbolic.\n");
        }
        out.append("\n");
        out.append("; Fatal grey-state query: sent cached metadata is validated after its key disappeared.\n");
        out.append("(declare-const witnessRound Int)\n");
        out.append("(declare-const witnessKey Int)\n");
        out.append("(assert (and (>= witnessRound 0) (<= witnessRound ").append(k).append(")))\n");
        out.append("(assert (= (dekKeyId (cachedDEK witnessRound)) witnessKey))\n");
        out.append(hasSend ? "(assert (send witnessRound))\n" : "; SEND_METADATA missing: send remains assumed by query.\n(assert (send witnessRound))\n");
        out.append(hasReceive ? "(assert (receive witnessRound))\n" : "; RECEIVE_METADATA missing: receive remains assumed by query.\n(assert (receive witnessRound))\n");
        out.append(hasValidation ? "(assert (validate witnessRound))\n" : "; VALIDATE missing: validate remains assumed by query.\n(assert (validate witnessRound))\n");
        out.append("(assert (not (hasKey witnessRound witnessKey)))\n");
        out.append("(assert (noEffectiveRecovery witnessRound))\n\n");
        out.append("; Extracted semantic evidence counts:\n");
        out.append("; events=").append(result.getEvents().size())
                .append(", summaries=").append(result.getTransitionSummaries().size())
                .append(", unknowns=").append(result.getUnknowns().size()).append("\n");
        out.append("(check-sat)\n");
        out.append("; Append (get-model) only after a SAT result.\n");
        return out.toString();
    }

    private boolean hasEvent(GreyStateAnalysisResult result, String eventType) {
        for (SemanticEvent event : result.getEvents()) {
            if (eventType.equals(event.getEventType())) {
                return true;
            }
        }
        return false;
    }

    private boolean hasEventInMethod(GreyStateAnalysisResult result, String eventType, String methodOwner) {
        for (SemanticEvent event : result.getEvents()) {
            if (eventType.equals(event.getEventType()) && event.getMethod().contains(methodOwner)) {
                return true;
            }
        }
        return false;
    }
}
