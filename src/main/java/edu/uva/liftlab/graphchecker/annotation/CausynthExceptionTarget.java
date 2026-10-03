package edu.uva.liftlab.graphchecker.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A known bug's marker on its target throw in a system tree:
 * {@code throw new @CausynthExceptionTarget("case-a,case-b") E();}, the value
 * the ids of the cases whose target the throw is, comma-separated.  No engine
 * code reads it -- a campaign's target is a class and a source line,
 * {@code exception_target:} in its target spec
 * (causynth.ExceptionTargetLineResolver) -- but the spec of a case without a
 * target.yaml is derived from it (tools/lib/annotated.py), and a sweep
 * counts a finding at a marked throw as that bug found again
 * (tools/adhoc/findings.py).  The trees compile against it
 * (external-callers.txt).  Class-retained, no runtime behavior.
 */
@Documented
@Retention(RetentionPolicy.CLASS)
@Target(ElementType.TYPE_USE)
public @interface CausynthExceptionTarget {
    String value() default "";
}
