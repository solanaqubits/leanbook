"""Bounded search for a linearization of completed, captured model operations.
This tests individual histories, not all executions. Unknown/pending histories must
be resolved or separately modeled; budget exhaustion is never success.
"""
from .store import normalize

def check_history(bridge,initial,history,final,*,budget=128):
    if any('output' not in h or h['end']<h['start'] for h in history):
        return {'status':'inconclusive','reason':'incomplete_history'}
    remaining_budget=budget
    exhausted=False
    def visit(image,remaining,order):
        nonlocal remaining_budget,exhausted
        if not remaining:
            return order if normalize(image)==normalize(final) else None
        for i in remaining:
            # Every completed-before-invocation predecessor must already have run.
            if any(history[j]['end']<history[i]['start'] for j in remaining if j!=i):continue
            if remaining_budget<=0:
                exhausted=True; return None
            remaining_budget-=1
            h=history[i]; ans=bridge.call(dict(image=image,input=h['input']))
            if ans['output']!=h['output']:continue
            found=visit(ans['image'],[j for j in remaining if j!=i],order+[i])
            if found is not None:return found
        return None
    order=visit(initial,list(range(len(history))),[])
    return {'status':'passed' if order is not None else ('inconclusive' if exhausted else 'failed'),
            'order':order,'evaluations':budget-remaining_budget}
