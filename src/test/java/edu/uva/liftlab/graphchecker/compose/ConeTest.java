package edu.uva.liftlab.graphchecker.compose;

import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.Assert.assertEquals;

/**
 * The open links of a claimed path's chain are cone.py's: what its fatal
 * condition names and no family of its selector binds, and what an arm the
 * witness chose holds -- never a value on the path the fatal does not rest
 * on.
 */
public class ConeTest {

    private static final String FORMULA = String.join("\n",
            "(set-logic ALL)",
            "(declare-const path_selector__0__a Bool)",
            "(declare-const path_selector__1__b Bool)",
            "(declare-const message_arm__0__x Bool)",
            "(declare-const M_I_field_HOFF.held Int)",
            "(declare-const M_I_field_HOFF.bound Int)",
            "(declare-const M_I_field_HOFF.off Int)",
            "(declare-const M_I_field_HOFF.viaDef Int)",
            "(declare-const M_I_field_HOFF.shadow Int)",
            "(declare-const M_I_field_HOFF.armHeld Int)",
            "(declare-const M_I_field_HOFF.other Int)",
            "; a comment (with parentheses",
            "(define-fun d ((p Int)) Bool (> (+ p M_I_field_HOFF.viaDef) 0))",
            "(assert (! (=> path_selector__0__a (and (> M_I_field_HOFF.held 1)"
                    + " (= M_I_field_HOFF.bound 2) (d 3)"
                    + " (let ((M_I_field_HOFF.shadow 5))"
                    + " (> M_I_field_HOFF.shadow 0)))) :named path_fatal__0))",
            "(assert (! (=> path_selector__0__a (and message_arm__0__x"
                    + " (=> message_arm__0__x (= M_I_field_HOFF.bound 7))))"
                    + " :named message_family__0__f))",
            // A hold on the path the fatal condition does not rest on.
            "(assert (=> path_selector__0__a (= M_I_field_HOFF.off 6)))",
            "(assert (! (=> path_selector__1__b (> M_I_field_HOFF.other 0))"
                    + " :named path_fatal__1))",
            "(check-sat)");

    @Test
    public void theOpenLinksAreWhatTheFatalRestsOnUnbound() {
        List<Composer.Concrete> concrete = Arrays.asList(
                // HELD in an arm the witness chose: open.
                row("HELD", "M_I_field_HOFF.armHeld").on("P0")
                        .in("message_arm__0__x"),
                // HELD on the path, outside the cone: closed.
                row("HELD", "M_I_field_HOFF.off").on("P0"),
                // FREE in an arm the witness did not choose: closed.
                row("FREE", "M_I_field_HOFF.other").on("P0")
                        .in("message_arm__0__y"),
                // An arm of another path: closed.
                row("HELD", "M_I_field_HOFF.armHeld").on("P1")
                        .in("message_arm__0__x"));
        Set<String> open = Cone.unbound(FORMULA, "path_selector__0__a", "P0",
                Collections.singleton("message_arm__0__x"), concrete);
        assertEquals("the fatal's own unbound v_H, one named through a"
                        + " define-fun, and the chosen arm's HELD one; not the"
                        + " family-bound, the let-bound, the hold the fatal"
                        + " does not rest on, nor another path's",
                new TreeSet<String>(Arrays.asList("M_I_field_HOFF.armHeld",
                        "M_I_field_HOFF.held", "M_I_field_HOFF.viaDef")),
                open);
        assertEquals("another path's own open link", Collections.singleton(
                "M_I_field_HOFF.other"), Cone.unbound(FORMULA,
                "path_selector__1__b", "P1",
                Collections.<String>emptySet(),
                Collections.<Composer.Concrete>emptyList()));
    }

    private static Composer.Concrete row(String kind, String subject) {
        return new Composer.Concrete(kind, subject, "6", "producer unstated",
                Collections.<String>emptyList());
    }
}
