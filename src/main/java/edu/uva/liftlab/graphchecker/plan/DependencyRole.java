package edu.uva.liftlab.graphchecker.plan;

/** The one role a region port can have ({@code dependencyRole}): it carries a
 *  value the solver may move. */
public final class DependencyRole {
    public static final String VALUE_FRONTIER = "VALUE_FRONTIER";

    private DependencyRole() {
    }
}
