"""Layout and scoped resource options for the reviewed generated Lean fixtures.

This is not a general Lean formatter. Generated fixtures are checked by Lean.
Literals and expected values are preserved; resource limits retain their values.
Unbreakable strings/comments remain unchanged for explicit review.
"""
def wrap_source(source, width=100):
    import re
    # Preserve existing resource options but scope them per declaration.
    options = re.findall(r'^set_option maxHeartbeats ([0-9]+)$', source, re.M)
    if len(set(options)) > 1:
        raise ValueError("Multiple heartbeat budgets require explicit per-section review")
    if options:
        source = re.sub(r'^set_option maxHeartbeats [0-9]+\n', '', source, flags=re.M)
        source = re.sub(r'^(?=(?:private |noncomputable )?(?:def |theorem |example |#eval ))',
                        'set_option maxHeartbeats '+options[-1]+' in\n-- Kernel reduction of fixed certificate fixtures retains the original heartbeat budget.\n', source, flags=re.M)
    source = re.sub(r'(/--(?:(?!-/).)*-/)\n(set_option maxHeartbeats [0-9]+ in\n--[^\n]*\n)',
                    r'\2\1\n', source, flags=re.S)
    marker='MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}'
    if any(len(line)>100 and marker in line for line in source.splitlines()):
        source=source.replace(marker,'migrationRegistry')
        lines=source.splitlines(keepends=True)
        idx=max(i+1 for i,line in enumerate(lines) if line.startswith('import '))
        lines.insert(idx, '\nprivate abbrev migrationRegistry :=\n  '+marker+'\n\n')
        source=''.join(lines)
    output=[]
    block=0
    for line in source.splitlines(keepends=True):
        text=line.rstrip('\r\n'); newline='\n' if line.endswith('\n') else ''
        if block or text.lstrip().startswith(('--','/-')):
            block += text.count('/-')-text.count('-/')
            output.append(text+newline); continue
        if len(text)<=width:
            output.append(text+newline); continue
        positions=[]; quoted=False; escaped=False
        for i,ch in enumerate(text):
            if quoted:
                if escaped:escaped=False
                elif ch=='\\':escaped=True
                elif ch=='"':quoted=False
                continue
            if ch=='"':quoted=True;continue
            if text[i:i+2] in ('--','/-'):break
            if ch.isspace() or ch == ',':positions.append(i+1)
        base=len(text)-len(text.lstrip());indent=' '*(base+2)
        tail=text;start=0;prefix=''
        while len(prefix+tail)>width:
            possible=[j for j in positions if start<j<=start+width-len(prefix) and text[start:j].strip()
                      and not text[:j].rstrip().endswith((':=', 'with', 'by'))
                      and (':= by' not in text or j <= text.index(':= by'))]
            if not possible:break
            cut=max(possible)
            output.append(prefix+text[start:cut].rstrip()+'\n')
            start=cut
            while start<len(text) and text[start].isspace():start+=1
            tail=text[start:]
            # Record field values/fields must remain indented inside the record.
            opened=text[:start].rfind('{')
            closed=text[:start].rfind('}')
            prefix=' '*(opened+2) if opened>closed and opened<70 else indent
        output.append(prefix+tail+newline)
    return ''.join(output)
