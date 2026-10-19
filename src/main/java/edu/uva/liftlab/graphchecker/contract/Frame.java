package edu.uva.liftlab.graphchecker.contract;

public final class Frame extends Value {
    private final String callSite;
    private final int iteration;

    private Frame(String callSite, int iteration) {
        this.callSite = callSite;
        this.iteration = iteration;
    }

    public static Frame of(String callSite, int iteration) {
        String site = Fields.text(callSite, "callSite");
        if (site.indexOf('/') >= 0 || site.indexOf('@') >= 0) {
            throw new IllegalArgumentException(
                    "a call site carries no '/' or '@': " + callSite);
        }
        return new Frame(site, Fields.nonNegative(iteration, "iteration"));
    }

    public static Frame parse(String rendered) {
        String value = rendered == null ? "" : rendered.trim();
        int marker = value.lastIndexOf('@');
        int iteration = Fields.trailingNumber(value, marker, 1);
        if (iteration < 0) {
            throw new IllegalArgumentException(
                    "not a <callSite>@<iteration>: " + rendered);
        }
        return of(value.substring(0, marker), iteration);
    }

    public String callSite() {
        return callSite;
    }

    public int iteration() {
        return iteration;
    }

    public String render() {
        return callSite + "@" + iteration;
    }

    @Override
    Object[] parts() {
        return new Object[] {callSite, iteration};
    }

    @Override
    public String toString() {
        return render();
    }
}
