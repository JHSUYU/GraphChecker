package edu.uva.liftlab.graphchecker.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * The marker the system trees' target throws still carry:
 * {@code throw new @CausynthExceptionTarget("id") E();}.  No engine code
 * reads it -- a case names its target by class and source line,
 * {@code exception_target:} in its target spec
 * (causynth.ExceptionTargetLineResolver) -- so it stays only as the trees'
 * compile ABI (external-callers.txt).  Class-retained, no runtime behavior.
 */
@Documented
@Retention(RetentionPolicy.CLASS)
@Target(ElementType.TYPE_USE)
public @interface CausynthExceptionTarget {
    String value() default "";
}
