package org.apache.hadoop.ipc;

import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime;

public final class CausynthSymbolicSource {
  private CausynthSymbolicSource() {
  }

  public static boolean symbolize(String sourceId, Object owner,
      String fieldSignature) {
    return ConcolicRegionRuntime.symbolizeConfiguredSourceField(
        sourceId, owner, fieldSignature);
  }
}
