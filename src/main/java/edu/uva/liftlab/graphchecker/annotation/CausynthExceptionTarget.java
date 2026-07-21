package edu.uva.liftlab.graphchecker.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Marks the exact exception construction that starts a Causynth analysis.
 *
 * <p>Java does not permit annotations directly on a {@code throw} statement,
 * so this annotation targets the constructed exception type:</p>
 *
 * <pre>{@code
 * throw new @CausynthExceptionTarget("request-failure") RequestException();
 * }</pre>
 *
 * <p>The marker is retained in the class file and has no runtime behavior.
 * The optional value is only needed when one analyzed class tree contains
 * more than one marked target.</p>
 */
@Documented
@Retention(RetentionPolicy.CLASS)
@Target(ElementType.TYPE_USE)
public @interface CausynthExceptionTarget {
    String value() default "";
}
