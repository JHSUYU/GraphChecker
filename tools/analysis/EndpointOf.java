import edu.uva.liftlab.graphchecker.contract.*;
import java.nio.file.*;
public class EndpointOf {
    public static void main(String[] a) throws Exception {
        SessionReader s = SessionReader.read(Paths.get(a[0]), a[1]);
        long seq = Long.parseLong(a[2]);
        for (WriteRow w : s.writes()) if (w.seq() == seq)
            System.out.println("WRITE " + w.endpoint().id() + "\t" + w.endpoint().activation());
        for (ReadRow r : s.reads()) if (r.seq() == seq)
            System.out.println("READ  " + r.endpoint().id() + "\t" + r.endpoint().activation());
    }
}
