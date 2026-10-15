package edu.uva.liftlab.graphchecker.explore;

import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.compose.SmtNames;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.ContentPort;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.ZkChain;

import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Which decisions EXPLORE may flip, as far as the iteration's ZooKeeper
 * chain goes ({@code zk_chain.jsonl}, {@link ZkChain}; its keys read off
 * the seed's composition, {@code compose.ZkKeysMain}).  A decision whose
 * symbolic sources are store values off the chain alone -- leaves of a
 * document no keys cover, reads of a store path or of a view of one the
 * chain does not hold -- is no flip: what it decides on is no value the
 * question rests on, and from the next replay on such a leaf crosses as a
 * constant.  A leaf of a chain path no keys row names is the whole
 * document's ({@link ZkChain#grown}).  No chain: every decision as before.
 */
final class ZkKeys {
    /** The chain's keyed paths' pointers, by slot; null: no chain. */
    private final Map<String, Set<String>> pointers;
    /** The slots of the chain's paths. */
    private final Set<String> paths = new HashSet<String>();

    private ZkKeys(ZkChain chain) {
        this.pointers = chain.empty() ? null : chain.pointers();
        for (String path : chain.paths()) {
            paths.add(path.substring(path.indexOf('\n') + 1));
        }
    }

    static ZkKeys of(ZkChain chain) {
        return new ZkKeys(chain);
    }

    /**
     * Whether a decision may be flipped as far as the chain goes: its term
     * names some symbol that is no off-chain store value (a root, a clock,
     * a message's field, a chain leaf, a read of a chain path or of
     * anything else), or names none it classifies.
     */
    boolean flippable(Corpus corpus, String sessionId, DecisionRow decision) {
        if (pointers == null) return true;
        String term = FlipQuery.statedTerm(corpus, sessionId,
                decision.term());
        SmtLowering lowering = corpus.lowering(sessionId);
        Set<String> symbols = new LinkedHashSet<String>();
        if (lowering != null) {
            symbols.addAll(lowering.reachedSymbols(
                    Collections.singletonList(term)));
        }
        SmtNames.symbols(term, symbols);
        boolean off = false;
        for (String symbol : symbols) {
            Corpus.SymbolKind kind = corpus.symbolKind(sessionId, symbol);
            if (kind == Corpus.SymbolKind.UNKNOWN) continue;
            if (kind == Corpus.SymbolKind.HANDOFF) {
                AttachRow attach = corpus.attach(sessionId, symbol);
                ContentPort.Parsed leaf = attach == null ? null
                        : ContentPort.parse(attach.endpoint().site());
                if (leaf != null && !onChain(leaf)) {
                    off = true;
                    continue;
                }
            } else if (kind == Corpus.SymbolKind.READ) {
                ReadRow read = corpus.read(sessionId, symbol);
                LocationKind location = read == null ? null
                        : read.location().kind();
                if ((location == LocationKind.STORE
                        || location == LocationKind.VIEW)
                        && !paths.contains(read.location().slot())
                        && !pointers.containsKey(read.location().slot())) {
                    off = true;
                    continue;
                }
            }
            return true;
        }
        return !off;
    }

    /** Whether the chain holds a leaf: its path's keys cover its pointer,
     *  or its path is the chain's with no keys (the whole document). */
    private boolean onChain(ContentPort.Parsed leaf) {
        Set<String> keys = pointers.get(leaf.location);
        if (keys == null) return paths.contains(leaf.location);
        return ContentPort.covers(keys, ContentPort.pointer(leaf.pointer));
    }
}
