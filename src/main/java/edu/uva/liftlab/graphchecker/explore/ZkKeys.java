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
 * the seed's composition, {@code compose.ZkKeysMain}).  The causal chain
 * alone decides which store values a flip may move (owner 2026-10-15:
 * weaving the classes that hold a node's view adds no flip): a decision is
 * one only where its term names a root, a message's field, a heap read, or
 * a chain read -- a leaf the chain's keys cover, a read of a chain path's
 * store or view.  Store values off the chain (leaves no key covers, reads
 * of a path or a view the chain does not hold), the containers a decode
 * builds, and nothing it classifies decide no flip: no value the question
 * rests on, and from the next replay on such a leaf crosses as a constant.
 * A leaf of a chain path no keys row names is the whole document's ({@link
 * ZkChain#grown}).  No chain: every decision as before.
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
     * names a root, a message's field, a heap read or a chain read.
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
        for (String symbol : symbols) {
            Corpus.SymbolKind kind = corpus.symbolKind(sessionId, symbol);
            if (kind == Corpus.SymbolKind.UNKNOWN) continue;
            if (kind == Corpus.SymbolKind.HANDOFF) {
                AttachRow attach = corpus.attach(sessionId, symbol);
                ContentPort.Parsed leaf = attach == null ? null
                        : ContentPort.parse(attach.endpoint().site());
                if (leaf != null && !onChain(leaf)) continue;
            } else if (kind == Corpus.SymbolKind.READ) {
                ReadRow read = corpus.read(sessionId, symbol);
                LocationKind location = read == null ? null
                        : read.location().kind();
                if ((location == LocationKind.STORE
                        || location == LocationKind.VIEW)
                        && !paths.contains(read.location().slot())
                        && !pointers.containsKey(read.location().slot())) {
                    continue;
                }
            }
            return true;
        }
        return false;
    }

    /** Whether the chain holds a leaf: its path's keys cover its pointer,
     *  or its path is the chain's with no keys (the whole document). */
    private boolean onChain(ContentPort.Parsed leaf) {
        Set<String> keys = pointers.get(leaf.location);
        if (keys == null) return paths.contains(leaf.location);
        return ContentPort.covers(keys, ContentPort.pointer(leaf.pointer));
    }
}
