package com.carrotsearch.randomizedtesting.annotations;

import java.lang.annotation.ElementType;
import java.lang.annotation.Inherited;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/** A test fixture with randomizedtesting's name: the runner reads it by
 *  name only (runtime/JUnitLifecycle#junit3Provided). */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
@Inherited
public @interface TestMethodProviders {
    Class<?>[] value();
}
