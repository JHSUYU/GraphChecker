package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;
import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

/**
 * WP4: a target is a class and a source line, resolved on class files javac
 * compiled from the fixture below -- a plain throw, two on one line with and
 * without the type, a lambda body, an anonymous class, a multi-line
 * {@code throw new}, a nested construction of the thrown type, a second
 * throw of one type (its ordinal), and lines that hold no throw.
 */
public class ExceptionTargetLineResolverTest {
    private static final String[] FIXTURE = {
        "package fx;",
        "public class Checks {",
        "  void plain(int x) {",
        "    if (x < 0) throw new IllegalStateException(\"negative\"); // @plain",
        "  }",
        "  void two(int x) {",
        "    if (x < 0) throw new IllegalStateException(\"a\"); else if (x > 9) throw new IllegalArgumentException(\"b\"); // @two",
        "  }",
        "  Runnable task(int x) {",
        "    return () -> {",
        "      if (x < 0) throw new IllegalStateException(\"lambda\"); // @lambda",
        "    };",
        "  }",
        "  Runnable anonymous(int x) {",
        "    return new Runnable() {",
        "      public void run() {",
        "        if (x < 0) throw new UnsupportedOperationException(\"anon\"); // @anonymous",
        "      }",
        "    };",
        "  }",
        "  void multiLine(int x) {",
        "    if (x < 0) {",
        "      throw new IllegalStateException( // @multiLine",
        "          String.valueOf(x) // @argument",
        "          + describe(x));",
        "    }",
        "  }",
        "  String describe(int x) { return \"x=\" + x; } // @noThrow",
        "  void nested(int x) {",
        "    if (x < 0) throw new IllegalStateException(new IllegalStateException(\"c\").getMessage()); // @nested",
        "  }",
        "  void second(int x) {",
        "    if (x < 0) throw new IllegalStateException(\"first\");",
        "    if (x > 9) throw new IllegalStateException(\"second\"); // @second",
        "  }",
        "  Exception kept() {",
        "    return new IllegalStateException(\"kept\"); // @notThrown",
        "  }",
        "}",
    };

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void aTargetLineResolvesToItsOneThrowOrIsRefusedByName()
            throws IOException {
        Path classes = compile();
        String ise = "java.lang.IllegalStateException";
        // marker, stated type, class, then the identity or the refusal code.
        String[][] rows = {
            {"plain", "", "fx.Checks", "fx.Checks#plain(I)V#new:" + ise + "#0"},
            {"two", "", "fx.Checks", "TARGET_LINE_AMBIGUOUS"},
            {"two", "IllegalArgumentException", "fx.Checks",
                "fx.Checks#two(I)V#new:java.lang.IllegalArgumentException#0"},
            {"two", ise, "fx.Checks", "fx.Checks#two(I)V#new:" + ise + "#0"},
            {"lambda", "", "fx.Checks",
                "fx.Checks#lambda$task$0(I)V#new:" + ise + "#0"},
            {"anonymous", "", "fx.Checks", "fx.Checks$1#run()V#new:"
                + "java.lang.UnsupportedOperationException#0"},
            {"multiLine", "", "fx.Checks",
                "fx.Checks#multiLine(I)V#new:" + ise + "#0"},
            {"argument", "", "fx.Checks", "TARGET_LINE_UNRESOLVED"},
            {"noThrow", "", "fx.Checks", "TARGET_LINE_UNRESOLVED"},
            {"nested", "", "fx.Checks", "fx.Checks#nested(I)V#new:" + ise + "#0"},
            {"second", "", "fx.Checks", "fx.Checks#second(I)V#new:" + ise + "#1"},
            {"notThrown", "", "fx.Checks", "TARGET_LINE_UNRESOLVED"},
            {"plain", "", "fx.Absent", "TARGET_LINE_UNRESOLVED"},
        };
        List<String> expected = new ArrayList<>();
        List<String> actual = new ArrayList<>();
        for (String[] row : rows) {
            ExceptionTargetLineResolver.TargetLine target =
                    new ExceptionTargetLineResolver.TargetLine("t-" + row[0],
                            row[2], line(row[0]), row[1]);
            String answer;
            try {
                ExceptionTargetSite site = ExceptionTargetLineResolver.locate(
                        Collections.singletonList(classes.toString()), target);
                assertEquals(target.name, site.id);
                answer = site.stableIdentity();
            } catch (IOException refusal) {
                answer = refusal.getMessage().split(":")[0];
            }
            expected.add(row[0] + " " + row[1] + " " + row[2] + " -> " + row[3]);
            actual.add(row[0] + " " + row[1] + " " + row[2] + " -> " + answer);
        }
        assertEquals(String.join("\n", expected), String.join("\n", actual));
    }

    private Path compile() throws IOException {
        File sources = folder.newFolder("src");
        File classes = folder.newFolder("classes");
        Path source = sources.toPath().resolve("fx/Checks.java");
        Files.createDirectories(source.getParent());
        Files.write(source, Arrays.asList(FIXTURE), StandardCharsets.UTF_8);
        JavaCompiler javac = ToolProvider.getSystemJavaCompiler();
        assertNotNull("the tests run on a JDK", javac);
        assertEquals(0, javac.run(null, null, null, "-d", classes.getPath(),
                source.toString()));
        return classes.toPath();
    }

    private static int line(String marker) {
        for (int i = 0; i < FIXTURE.length; i++) {
            if (FIXTURE[i].endsWith("// @" + marker)) {
                return i + 1;
            }
        }
        throw new AssertionError("no fixture line @" + marker);
    }
}
