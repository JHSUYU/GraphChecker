package edu.uva.liftlab.graphchecker;

import soot.G;
import soot.LambdaMetaFactory;
import soot.Singletons;
import soot.SootClass;
import soot.SootMethodRef;
import soot.Type;
import soot.Value;

import java.lang.reflect.Field;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;

/**
 * Names the class Soot desugars a lambda into by what the class is, not by
 * when it was made.
 *
 * <p>Soot names that class {@code <Outer>$<impl>__<n>} ({@code <impl>} the
 * implementation method, {@code $} as {@code _}), with {@code n} from one
 * counter over the whole run, in the order bodies happen to be built.  Bodies
 * built on several threads, a process dir listed in another order, or another
 * scope (a weave adds the lineage classes) give the same lambda another name,
 * and with it another region id, other site ids and other Jimple, in the
 * static artifacts and the woven classes alike.  Installed as Soot's
 * {@code LambdaMetaFactory}, this one sets {@code n} to a hash of everything
 * the class is made from (the enclosing class, the bootstrap arguments, the
 * interface method and the captured types), so a lambda has one name in every
 * run.  Two call sites that would make the same class share it.</p>
 *
 * <p>Two different classes whose names still collide (one implementation
 * method, two contents, one 31-bit hash) stop the run: Soot refuses the
 * second as a duplicate class.</p>
 */
final class LambdaClassNames extends LambdaMetaFactory {
    /** Soot's counter: the next class is numbered {@code ++uniq}. */
    private static final Field COUNTER = field(LambdaMetaFactory.class,
            "uniq");

    /** The bootstrap method of the class made for each content. */
    private final Map<String, SootMethodRef> made = new HashMap<>();

    private LambdaClassNames(Singletons.Global global) {
        super(global);
    }

    /**
     * Makes this Soot's lambda factory: after the classes are loaded (the
     * factory resolves the boxing methods), before any body is built.
     */
    static void install() {
        Field factory = field(Singletons.class,
                "instance_soot_LambdaMetaFactory");
        Field global = field(Singletons.class, "g");
        try {
            if (factory.get(G.v()) != null) {
                throw new IllegalStateException("Soot's own lambda factory "
                        + "ran before the lambda class names were installed");
            }
            factory.set(G.v(), new LambdaClassNames(
                    (Singletons.Global) global.get(G.v())));
        } catch (IllegalAccessException refused) {
            throw new IllegalStateException(
                    "cannot install the lambda class names", refused);
        }
    }

    @Override
    public synchronized SootMethodRef makeLambdaHelper(
            List<? extends Value> bootstrapArgs, int tag, String name,
            Type[] types, SootClass enclosingClass) {
        String content = enclosingClass.getName() + '\n' + tag + '\n' + name
                + '\n' + Arrays.toString(types) + '\n' + bootstrapArgs;
        SootMethodRef bootstrap = made.get(content);
        if (bootstrap != null) return bootstrap;
        long bits = UUID.nameUUIDFromBytes(
                content.getBytes(StandardCharsets.UTF_8))
                .getMostSignificantBits();
        int number = 1 + (int) ((bits >>> 1) % Integer.MAX_VALUE);
        try {
            COUNTER.setInt(this, number - 1);
        } catch (IllegalAccessException refused) {
            throw new IllegalStateException(
                    "cannot number the lambda class", refused);
        }
        bootstrap = super.makeLambdaHelper(bootstrapArgs, tag, name, types,
                enclosingClass);
        // Null: Soot declined the call site, and made no class.
        if (bootstrap == null) return null;
        String className = bootstrap.getDeclaringClass().getName();
        if (!className.endsWith("__" + number)) {
            throw new IllegalStateException("Soot named the lambda class "
                    + className + ", not by its number " + number);
        }
        made.put(content, bootstrap);
        return bootstrap;
    }

    private static Field field(Class<?> owner, String name) {
        try {
            Field field = owner.getDeclaredField(name);
            field.setAccessible(true);
            return field;
        } catch (NoSuchFieldException missing) {
            throw new IllegalStateException("this Soot has no " + owner
                    .getName() + "." + name, missing);
        }
    }
}
