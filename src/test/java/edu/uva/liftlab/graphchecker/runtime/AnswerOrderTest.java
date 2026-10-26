package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import org.junit.Test;

public class AnswerOrderTest {
    private static final String NODE = "t/master0#epoch0";
    private static final String[] GROUPS = {"METHOD\nREGION.p\n<a.P: void p()>",
        "METHOD\nREGION.p\n<a.P: void q()>"};

    private static final class Row implements AnswerOrder.Planned {
        final OccurrenceAddress address;
        final List<String> shape;
        final Set<String> recordedBeside = new LinkedHashSet<String>();
        final long rootCall;
        final String group;
        boolean reserved;
        boolean live;
        boolean shapedLive;
        boolean compatible;

        Row(OccurrenceAddress address, List<String> shape, long rootCall,
            String group) {
            this.address = address;
            this.shape = shape;
            this.rootCall = rootCall;
            this.group = group;
        }

        @Override
        public OccurrenceAddress address() {
            return address;
        }

        @Override
        public List<String> shape() {
            return shape;
        }

        @Override
        public Set<String> recordedBeside() {
            return recordedBeside;
        }

        @Override
        public long recordedRootCall() {
            return rootCall;
        }

        @Override
        public String rootHookGroup() {
            return group;
        }
    }

    private static final class Refused {
        final OccurrenceAddress observed;
        final String name;

        Refused(OccurrenceAddress observed, String name) {
            this.observed = observed;
            this.name = name;
        }
    }

    private static OccurrenceAddress address(String api, int k, int frame) {
        return OccurrenceAddress.of(NodeId.parse(NODE), "REGION.p",
                CausalContext.of(Role.of("CLIENT"), api, k), frame < 0
                ? ExecutionIndex.empty() : ExecutionIndex.of(
                Collections.singletonList(Frame.of("<a.P: void p()>#u1",
                        frame))));
    }

    private static Function<CausalContext, List<String>> shapes() {
        return context -> Collections.singletonList("Root:CLIENT/"
                + ((CausalContext.Root) context).api());
    }

    private static final class Table {
        final List<Row> rows = new ArrayList<Row>();
        final OccurrenceAddress observed;
        final boolean openedNone;
        final String key;
        final List<String> said = new ArrayList<String>();

        Table(long seed) {
            Random random = new Random(seed);
            int size = 1 + random.nextInt(6);
            for (int index = 0; index < size; index++) {
                List<String> shape = random.nextInt(4) == 0
                        ? Collections.<String>emptyList()
                        : Collections.singletonList("Root:CLIENT/"
                        + (random.nextInt(3) == 0 ? "other" : "test"));
                Row row = new Row(address(random.nextInt(4) == 0 ? "other"
                        : "test", 1 + random.nextInt(4),
                        random.nextInt(3) - 1), shape,
                        random.nextInt(6) - 1, GROUPS[random.nextInt(4) == 0
                        ? 1 : 0]);
                row.reserved = random.nextInt(5) == 0;
                row.live = random.nextInt(4) == 0;
                row.compatible = random.nextInt(6) != 0;
                rows.add(row);
            }
            observed = random.nextInt(3) == 0
                    ? rows.get(random.nextInt(size)).address
                    : address(random.nextInt(4) == 0 ? "other" : "test",
                    1 + random.nextInt(5), random.nextInt(3) - 1);
            for (Row row : rows) {
                if (random.nextInt(5) == 0) row.recordedBeside.add(observed.id());
            }
            openedNone = random.nextInt(6) == 0;
            key = GROUPS[random.nextInt(5) == 0 ? 1 : 0];
        }

        Refused refusal(int index) {
            Row task = rows.get(index);
            if (!task.compatible) return new Refused(null, "incompatible" + index);
            return task.address.id().equals(observed.id()) ? null
                    : new Refused(observed, "address" + index);
        }

        void note(int index, Refused refused) {
            said.add("note " + index + " " + refused.name);
        }

        void recordedNote(int index, Refused refused) {
            said.add("recorded " + index + " " + refused.name);
        }

        void take(int index, boolean byShape) {
            rows.get(index).live = true;
            rows.get(index).shapedLive = byShape;
            said.add("take " + index + " " + byShape);
        }

        String parent() {
            Function<CausalContext, List<String>> shapes = shapes();
            int answering = -1;
            Refused answered = null;
            for (int index = 0; index < rows.size(); index++) {
                Row task = rows.get(index);
                if (!task.group.equals(key)) continue;
                if (task.reserved) continue;
                Refused refused = refusal(index);
                if (refused != null) {
                    if (!task.live && parentAnswers(task, refused.observed,
                            shapes) && (answering < 0
                            || parentEarlier(task, rows.get(answering)))) {
                        if (answering >= 0) note(answering, answered);
                        answering = index;
                        answered = refused;
                        continue;
                    }
                    note(index, refused);
                    continue;
                }
                if (task.live) continue;
                take(index, false);
                if (answered != null) note(answering, answered);
                return index + " " + said;
            }
            if (answering < 0) return -1 + " " + said;
            Row earliest = rows.get(answering);
            if (earliest.recordedBeside.contains(answered.observed.id())) {
                recordedNote(answering, answered);
                return -1 + " " + said;
            }
            if (parentOccupies(key, answered.observed) || openedNone) {
                note(answering, answered);
                return -1 + " " + said;
            }
            take(answering, true);
            return answering + " " + said;
        }

        private boolean parentAnswers(Row task, OccurrenceAddress observed,
                                      Function<CausalContext, List<String>>
                                              shapes) {
            return !task.shape.isEmpty() && task.address != null
                    && observed != null
                    && observed.regionId().equals(task.address.regionId())
                    && observed.node().equals(task.address.node())
                    && ContextShape.answers(observed, task.address,
                    shapes.apply(observed.context()), task.shape);
        }

        private boolean parentEarlier(Row task, Row other) {
            return task.rootCall >= 0L && (other.rootCall < 0L
                    || task.rootCall < other.rootCall);
        }

        private boolean parentOccupies(String group,
                                       OccurrenceAddress address) {
            for (Row task : rows) {
                if (task.address != null && task.group.equals(group)
                        && task.address.regionId().equals(address.regionId())
                        && task.address.node().equals(address.node())
                        && task.address.context().render().equals(
                        address.context().render())) {
                    return true;
                }
            }
            return false;
        }

        String shared() {
            int index = AnswerOrder.select(new AnswerOrder.Offer<Refused>() {
                @Override
                public List<Row> tasks() {
                    return rows;
                }

                @Override
                public boolean offered(int at) {
                    return rows.get(at).group.equals(key)
                            && !rows.get(at).reserved;
                }

                @Override
                public Refused refusal(int at) {
                    return Table.this.refusal(at);
                }

                @Override
                public OccurrenceAddress observed(Refused refused) {
                    return refused.observed;
                }

                @Override
                public boolean live(int at) {
                    return rows.get(at).live;
                }

                @Override
                public void take(int at, boolean byShape) {
                    Table.this.take(at, byShape);
                }

                @Override
                public void unaddressed(int at, Refused refused) {
                    note(at, refused);
                }

                @Override
                public void recordedHere(int at, Refused refused) {
                    recordedNote(at, refused);
                }

                @Override
                public boolean openedNone() {
                    return openedNone;
                }
            }, shapes());
            return index + " " + said;
        }
    }

    @Test
    public void theSharedOrderRuleChoosesAndNotesAsTheParentsSelectDid() {
        int byShape = 0;
        int exact = 0;
        int none = 0;
        for (long seed = 0; seed < 20000; seed++) {
            String parent = new Table(seed).parent();
            String shared = new Table(seed).shared();
            assertEquals("table " + seed, parent, shared);
            if (shared.contains("true]")) {
                byShape++;
            } else if (shared.startsWith("-1")) {
                none++;
            } else {
                exact++;
            }
        }
        assertTrue("every outcome is drawn: " + byShape + " by shape, "
                + exact + " by address, " + none + " none",
                byShape > 500 && exact > 500 && none > 500);
    }
}
