package edu.uva.liftlab.graphchecker;

import soot.FastHierarchy;
import soot.G;
import soot.LambdaMetaFactory;
import soot.Scene;
import soot.Singletons;
import soot.SootClass;
import soot.SootMethodRef;
import soot.Type;
import soot.Value;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;
import soot.util.MultiMap;

final class LambdaClassNames extends LambdaMetaFactory {
    private static final Field COUNTER = field(LambdaMetaFactory.class,
            "uniq");

    private final Map<String, SootMethodRef> made = new HashMap<>();

    private LambdaClassNames(Singletons.Global global) {
        super(global);
    }

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
        if (bootstrap == null) return null;
        String className = bootstrap.getDeclaringClass().getName();
        if (!className.endsWith("__" + number)) {
            throw new IllegalStateException("Soot named the lambda class "
                    + className + ", not by its number " + number);
        }
        made.put(content, bootstrap);
        return bootstrap;
    }

    private static final Field SUBCLASSES = field(FastHierarchy.class,
            "classToSubclasses");
    private static final Field IMPLEMENTERS = field(FastHierarchy.class,
            "interfaceToImplementers");
    private static final Field ALL_IMPLEMENTERS = field(FastHierarchy.class,
            "interfaceToAllImplementers");
    private static final Field INTERVALS = field(FastHierarchy.class,
            "classToInterval");
    private static final Method DFS = method(FastHierarchy.class, "dfsVisit",
            int.class, SootClass.class);

    @Override
    @SuppressWarnings("unchecked")
    protected void addClassAndInvalidateHierarchy(SootClass made) {
        Scene scene = Scene.v();
        FastHierarchy hierarchy = scene.hasFastHierarchy()
                ? scene.getFastHierarchy() : null;
        boolean current = hierarchy != null && resolved(scene) == resolved;
        scene.addClass(made);
        resolved = resolved(scene);
        if (!current) return;
        if (made.isInterface()) {
            throw new IllegalStateException("Soot made the lambda class "
                    + made.getName() + " an interface");
        }
        try {
            SootClass parent = made.getSuperclassUnsafe();
            if (parent != null) {
                ((MultiMap<SootClass, SootClass>) SUBCLASSES.get(hierarchy))
                        .put(parent, made);
            }
            MultiMap<SootClass, SootClass> implementers =
                    (MultiMap<SootClass, SootClass>) IMPLEMENTERS.get(hierarchy);
            for (SootClass type : made.getInterfaces()) {
                implementers.put(type, made);
            }
            ((MultiMap<SootClass, SootClass>) ALL_IMPLEMENTERS.get(hierarchy))
                    .clear();
            ((Map<SootClass, ?>) INTERVALS.get(hierarchy)).clear();
            int next = (Integer) DFS.invoke(hierarchy, 0,
                    scene.getObjectType().getSootClass());
            for (SootClass phantom
                    : new ArrayList<>(scene.getPhantomClasses())) {
                if (!phantom.isInterface()) {
                    next = (Integer) DFS.invoke(hierarchy, next, phantom);
                }
            }
        } catch (IllegalAccessException | InvocationTargetException refused) {
            throw new IllegalStateException("cannot add the lambda class "
                    + made.getName() + " to the hierarchy", refused);
        }
        scene.setFastHierarchy(hierarchy);
    }

    private int resolved = -1;

    private static int resolved(Scene scene) {
        int count = 0;
        for (SootClass type : scene.getClasses()) {
            if (type.resolvingLevel() >= SootClass.HIERARCHY) count++;
        }
        return count;
    }

    private static Method method(Class<?> owner, String name,
                                 Class<?>... parameters) {
        try {
            Method method = owner.getDeclaredMethod(name, parameters);
            method.setAccessible(true);
            return method;
        } catch (NoSuchMethodException missing) {
            throw new IllegalStateException("this Soot has no " + owner
                    .getName() + "." + name, missing);
        }
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
