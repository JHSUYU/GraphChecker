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

final class ZkKeys {
    private final Map<String, Set<String>> pointers;
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
        boolean offChain = false;
        for (String symbol : symbols) {
            Corpus.SymbolKind kind = corpus.symbolKind(sessionId, symbol);
            if (kind == Corpus.SymbolKind.UNKNOWN) continue;
            if (kind == Corpus.SymbolKind.HANDOFF) {
                AttachRow attach = corpus.attach(sessionId, symbol);
                ContentPort.Parsed leaf = attach == null ? null
                        : ContentPort.parse(attach.endpoint().site());
                if (leaf != null && !onChain(leaf)) {
                    offChain = true;
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
                    offChain = true;
                    continue;
                }
            }
            return true;
        }
        return !offChain;
    }

    private boolean onChain(ContentPort.Parsed leaf) {
        Set<String> keys = pointers.get(leaf.location);
        if (keys == null) return paths.contains(leaf.location);
        return ContentPort.covers(keys, ContentPort.pointer(leaf.pointer));
    }
}
