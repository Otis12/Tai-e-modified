package pascal.taie.analysis.pta.plugin.container;

import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.util.Map;
import java.util.Set;

public class Host  {
    private final Obj obj;

    private boolean taint;

    private final int index;

    private final Map<String, Set<Var>> relatedArguments = Maps.newMap();

    private final Map<String, Set<Var>> relatedResults = Maps.newMap();

    public enum Classification {
        MAP, COLLECTION
    }

    private Classification classification;

    public Host(Obj obj, int index, Classification classification) {
        this.obj = obj;
        this.index = index;
        this.classification = classification;
        taint = false;
        relatedArguments.put("Map-Value", Sets.newSet());
        relatedArguments.put("Map-Key", Sets.newSet());
        relatedArguments.put("Col-Value", Sets.newSet());
        relatedResults.put("Map-Value", Sets.newSet());
        relatedResults.put("Map-Key", Sets.newSet());
        relatedResults.put("Col-Value", Sets.newSet());
    }

    public void setTaint() {
        taint = true;
    }

    public boolean getTaint() {
        return taint;
    }

    public int getIndex() {
        return index;
    }

    public boolean addInArgument(Var var, String category) {
        Set<Var> arguments = relatedArguments.get(category);
        if (arguments == null)
            throw new AnalysisException("Invalid Category!");
        return arguments.add(var);
    }


    public boolean addOutResult(Var var, String category) {
        Set<Var> results = relatedResults.get(category);
        return results != null && results.add(var);
    }

    public Obj getObject() {
        return obj;
    }

    public Type getType() {
        return obj.getType();
    }

    public Classification getClassification() {
        return classification;
    }

    @Override
    public String toString() {
        return "Host-Object{" + obj.toString() + "}";
    }
}
