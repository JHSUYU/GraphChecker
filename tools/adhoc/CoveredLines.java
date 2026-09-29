import java.io.*;
import java.util.*;
import org.jacoco.core.analysis.*;
import org.jacoco.core.tools.ExecFileLoader;

/** CoveredLines EXEC CLASSDIR... : "class<TAB>line" for every line with an executed instruction. */
public class CoveredLines {
    public static void main(String[] a) throws Exception {
        ExecFileLoader loader = new ExecFileLoader();
        loader.load(new File(a[0]));
        CoverageBuilder builder = new CoverageBuilder();
        Analyzer analyzer = new Analyzer(loader.getExecutionDataStore(), builder);
        for (int i = 1; i < a.length; i++) analyzer.analyzeAll(new File(a[i]));
        PrintStream out = new PrintStream(new BufferedOutputStream(System.out));
        for (IClassCoverage c : builder.getClasses()) {
            if (c.getInstructionCounter().getCoveredCount() == 0) continue;
            for (int l = c.getFirstLine(); l <= c.getLastLine(); l++) {
                int s = c.getLine(l).getStatus();
                if (s == ICounter.FULLY_COVERED || s == ICounter.PARTLY_COVERED) {
                    out.println(c.getName() + "\t" + l);
                }
            }
        }
        out.flush();
    }
}
