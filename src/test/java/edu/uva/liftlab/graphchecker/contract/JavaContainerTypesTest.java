package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class JavaContainerTypesTest {
    @Test
    public void classifiesSymbolicResultOperations() {
        assertTrue(JavaContainerTypes.symbolicResultOperation(
                "<java.util.Map: java.lang.Object get(java.lang.Object)>"));
        assertTrue(JavaContainerTypes.symbolicResultOperation(
                "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>"));
        assertTrue(JavaContainerTypes.symbolicResultOperation(
                "<java.util.List: java.lang.Object get(int)>"));
        assertTrue(JavaContainerTypes.symbolicResultOperation(
                "<java.util.Set: boolean add(java.lang.Object)>"));

        assertTrue(JavaContainerTypes.symbolicResultOperation(
                "<java.util.Iterator: java.lang.Object next()>"));
        assertFalse(JavaContainerTypes.symbolicResultOperation(
                "<java.util.Map: void clear()>"));
        assertFalse(JavaContainerTypes.symbolicResultOperation(
                "<example.State: java.lang.Object get(java.lang.Object)>"));
    }

    @Test
    public void classifiesOnlyExactModeledMutators() {
        assertTrue(JavaContainerTypes.modeledContainerMutator(
                "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>"));
        assertTrue(JavaContainerTypes.modeledContainerMutator(
                "<java.util.List: java.lang.Object set(int,java.lang.Object)>"));
        assertTrue(JavaContainerTypes.modeledContainerMutator(
                "<java.util.Set: boolean add(java.lang.Object)>"));

        assertFalse(JavaContainerTypes.modeledContainerMutator(
                "<java.util.Map: java.lang.Object get(java.lang.Object)>"));
        assertFalse(JavaContainerTypes.modeledContainerMutator(
                "<java.util.Map: int size()>"));
        assertFalse(JavaContainerTypes.modeledContainerMutator(
                "<example.State: java.lang.Object put(java.lang.Object,java.lang.Object)>"));
    }

    @Test
    public void distinguishesStructuralPredicatesFromSemanticLookups() {
        assertTrue(JavaContainerTypes.structuralIterationPredicate(
                "<java.util.Iterator: boolean hasNext()>"));
        assertTrue(JavaContainerTypes.structuralIterationPredicate(
                "<java.util.Enumeration: boolean hasMoreElements()>"));
        assertTrue(JavaContainerTypes.structuralCardinalityOperation(
                "<java.util.Collection: int size()>"));
        assertTrue(JavaContainerTypes.structuralCardinalityOperation(
                "<java.util.Map: boolean isEmpty()>"));

        assertFalse(JavaContainerTypes.structuralIterationPredicate(
                "<java.util.Iterator: java.lang.Object next()>"));
        assertFalse(JavaContainerTypes.structuralCardinalityOperation(
                "<java.util.Map: boolean containsKey(java.lang.Object)>"));
        assertFalse(JavaContainerTypes.structuralCardinalityOperation(
                "<example.State: int size()>"));
    }

    @Test
    public void identifiesOnlyExactAssociativePut() {
        assertTrue(JavaContainerTypes.associativePut(
                "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>"));
        assertTrue(JavaContainerTypes.associativePut(
                "<java.util.HashMap: java.lang.Object put(java.lang.Object,java.lang.Object)>"));
        assertFalse(JavaContainerTypes.associativePut(
                "<java.util.Map: java.lang.Object remove(java.lang.Object)>"));
        assertFalse(JavaContainerTypes.associativePut(
                "<example.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>"));
    }
}
