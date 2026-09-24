package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * One read held to the write it observes: a version a world chose.
 *
 * <p>A shared location holds many versions, and a read observes the one that
 * is live when it runs.  In the recording the interleaving of the threads
 * decided which; in a world, z3 decides among the writers the read could
 * have observed ({@code smt.Arms#stateArms}), and the recording's own choice
 * stands wherever the writer ran on another thread than the reader.  A replay
 * of that world holds the read until this writer's version is live and holds
 * any other write to the location until the read has observed it
 * ({@code runtime.Versions}); a choice it cannot realize is unreachable.</p>
 *
 * <p>Both ends are endpoints, named the way the rows name them: the read and
 * write sites are the VM's ({@link Endpoint#stateSite}), and the ids are what
 * a replay computes for the same events.</p>
 */
public final class ReadsFrom {
    private final String reader;
    private final String readerSite;
    private final String writer;
    private final String writerSite;

    private ReadsFrom(String reader, String readerSite, String writer,
                      String writerSite) {
        this.reader = reader;
        this.readerSite = readerSite;
        this.writer = writer;
        this.writerSite = writerSite;
    }

    public static ReadsFrom of(Endpoint reader, Endpoint writer) {
        Fields.required(reader, "reader");
        Fields.required(writer, "writer");
        return of(reader.id(), reader.site(), writer.id(), writer.site());
    }

    public static ReadsFrom of(String reader, String readerSite,
                               String writer, String writerSite) {
        return new ReadsFrom(Fields.text(reader, "reader"),
                Fields.text(readerSite, "readerSite"),
                Fields.text(writer, "writer"),
                Fields.text(writerSite, "writerSite"));
    }

    /** The reader's endpoint id. */
    public String reader() {
        return reader;
    }

    /** The reader's site, {@code class#method(desc)#bci:READ}. */
    public String readerSite() {
        return readerSite;
    }

    /** The endpoint id of the write the read observes. */
    public String writer() {
        return writer;
    }

    /** The writer's site, {@code class#method(desc)#bci:WRITE}. */
    public String writerSite() {
        return writerSite;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof ReadsFrom)) return false;
        ReadsFrom other = (ReadsFrom) value;
        return reader.equals(other.reader) && writer.equals(other.writer)
                && readerSite.equals(other.readerSite)
                && writerSite.equals(other.writerSite);
    }

    @Override
    public int hashCode() {
        return Objects.hash(reader, readerSite, writer, writerSite);
    }

    @Override
    public String toString() {
        return reader + " <- " + writer;
    }
}
