/**
 * This is a mock for JMethod that only used for PhantomSink.
 * Using the mock JMethod in Point Analysis or other scenarios may cause problem.
 *
 */




package pascal.taie.analysis.pta.plugin.taint;

import pascal.taie.ir.IR;
import pascal.taie.language.annotation.Annotation;
import pascal.taie.language.annotation.AnnotationHolder;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Modifier;
import pascal.taie.language.generics.GSignatures;
import pascal.taie.language.generics.MethodGSignature;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.ir.proginfo.MethodRef;

import javax.annotation.Nullable;
import java.util.*;

public class MockJMethod extends JMethod {

    public MockJMethod(JClass declaringClass, String name, Set<Modifier> modifiers, List<Type> paramTypes, Type returnType){
        super(declaringClass, name, modifiers, paramTypes, returnType, new ArrayList<>(), null, AnnotationHolder.emptyHolder(), null, null, new Object());
//        Set<Modifier> modifiers = new HashSet<>();
//        modifiers.add(Modifier.PUBLIC);
//        List<ClassType> exceptions = new ArrayList<>();
//        MethodGSignature methodGSignature = null;
//        AnnotationHolder annotationHolder = AnnotationHolder.emptyHolder();
//        List<AnnotationHolder> paramAnnotations = null;
//        List<String> paramNames = null;
//        Object methodSource = new Object();

//        super.modifiers.add(Modifier.PUBLIC);

    }


    public MockJMethod(MethodRef methodRef,Set<Modifier> modifiers){
        super(methodRef.getDeclaringClass(),methodRef.getName(),modifiers,methodRef.getParameterTypes(),methodRef.getReturnType(),new ArrayList<>(),null,AnnotationHolder.emptyHolder(),null, null, new Object());
    }


//    public void fromMethodRef(MethodRef methodRef){
//
//    }

    @Override
    public IR getIR() {

        return null;
    }
}
