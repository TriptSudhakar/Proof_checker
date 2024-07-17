import re
import sys

def checkProof(filename):
    with open(filename,"r") as f:
        l = f.readlines()

    statement = l[0]
    [premises,sequent] = statement.split("|-")
    premise_list = premises.split(",")
    sequent = (sequent.strip()).replace(" ","")
    premise_list = [(x.strip()).replace(" ","") for x in premise_list]

    line_dict = {}
    explanations = {}
    proof = l[2:]
    for i in range(len(proof)):
        proof[i] = proof[i].split(']')
        proof[i][0] = proof[i][0]+']'
        proof[i][0] = proof[i][0].replace(" ","")
        proof[i][1] = (proof[i][1].strip()).replace(" ","")
        explanations[i+3] = proof[i][0]
        line_dict[i+3] = proof[i][1]

    valid = True

    for i in range(len(proof)):
        if not valid: break
        reason = proof[i][0]
        argument = proof[i][1]
        number = i+3
        # print(argument)

        if reason == "[premise]":
            if argument not in premise_list: valid = False
        
        elif reason == "[assumption]": continue
        
        elif reason == "[lem]":
            pos = argument[1:len(argument)//2-2]
            if argument != '('+pos+'\\/'+'(!'+pos+'))': valid = False

        elif re.match(r'^\[copy\d+\]$',reason):
            match = re.search(r'\d+',reason)
            line_no = int(reason[match.start():match.end()])
            if line_no>number or line_dict[line_no] != argument : valid = False
        
        elif re.match(r'^\[mp\d+,\d+\]$',reason):
            match = re.search(r'\d+,',reason)
            first = int(reason[match.start():match.end()-1])
            match = re.search(r'\d+\]',reason)
            second = int(reason[match.start():match.end()-1])
            if first>number or second>number or line_dict[second] != '('+line_dict[first]+'->'+argument+')': valid = False
        
        elif re.match(r'^\[mt\d+,\d+\]$',reason):
            match = re.search(r'\d+,',reason)
            first = int(reason[match.start():match.end()-1])
            match = re.search(r'\d+\]',reason)
            second = int(reason[match.start():match.end()-1])
            if first>number or second>number or argument[1] != '!' or line_dict[second][1] != '!' or line_dict[first] != '('+argument[2:-1]+'->'+line_dict[second][2:-1]+')': valid = False

        elif re.match(r'^\[and-in\d+,\d+\]$',reason):
            match = re.search(r'\d+,',reason)
            first = int(reason[match.start():match.end()-1])
            match = re.search(r'\d+\]',reason)
            second = int(reason[match.start():match.end()-1])
            if first>number or second>number or argument != '('+line_dict[first]+'/\\'+line_dict[second]+')': valid = False

        elif re.match(r'^\[and-e1\d+\]$',reason):
            match = re.search(r'\d+\]',reason)
            line_no = int(reason[match.start()+1:match.end()-1])
            index = line_dict[line_no].find(argument+"/\\")
            if line_no>number or index==-1: valid = False

        elif re.match(r'^\[and-e2\d+\]$',reason):
            match = re.search(r'\d+\]',reason)
            line_no = int(reason[match.start()+1:match.end()-1])
            index = line_dict[line_no].find("/\\"+argument)
            if line_no>number or index==-1: valid = False
        
        elif re.match(r'^\[or-in1\d+\]$',reason):
            match = re.search(r'\d+\]',reason)
            line_no = int(reason[match.start()+1:match.end()-1])
            index = argument.find(line_dict[line_no]+"\\/")
            if line_no>number or index==-1: valid = False

        elif re.match(r'^\[or-in2\d+\]$',reason):
            match = re.search(r'\d+\]',reason)
            line_no = int(reason[match.start()+1:match.end()-1])
            index = argument.find("\\/"+line_dict[line_no])
            if line_no>number or index==-1: valid = False

        elif re.match(r'^\[dneg-in\d+\]$',reason):
            match = re.search(r'\d+',reason)
            line_no = int(reason[match.start():match.end()])
            if line_no>number or '(!(!'+line_dict[line_no]+'))' != argument: valid = False

        elif re.match(r'^\[dneg-el\d+\]$',reason):
            match = re.search(r'\d+',reason)
            line_no = int(reason[match.start():match.end()])
            if line_no>number or '(!(!'+argument+'))' != line_dict[line_no]: valid = False

        elif re.match(r'^\[bot-el\d+\]$',reason):
            match = re.search(r'\d+',reason)
            line_no = int(reason[match.start():match.end()])
            if line_no>number or line_dict[line_no]!="\\bot": valid = False

        elif re.match(r'^\[neg-el\d+,\d+\]$',reason):
            match = re.search(r'\d+,',reason)
            first = int(reason[match.start():match.end()-1])
            match = re.search(r'\d+\]',reason)
            second = int(reason[match.start():match.end()-1])
            if first>number or second>number or argument!="\\bot" or '(!'+line_dict[first]+')'!=line_dict[second]: valid = False

        elif re.match(r'^\[neg-in\d+-\d+\]$',reason):
            match = re.search(r'\d+-',reason)
            first = int(reason[match.start():match.end()-1])
            match = re.search(r'\d+\]',reason)
            second = int(reason[match.start():match.end()-1])
            if first>number or second>number or proof[first-3][0]!="[assumption]" or line_dict[second]!="\\bot" or '(!'+line_dict[first]+')'!=argument: valid = False

        elif re.match(r'^\[pbc\d+-\d+\]$',reason):
            match = re.search(r'\d+-',reason)
            first = int(reason[match.start():match.end()-1])
            match = re.search(r'\d+\]',reason)
            second = int(reason[match.start():match.end()-1])
            if first>number or second>number or proof[first-3][0]!="[assumption]" or line_dict[second]!="\\bot" or '(!'+argument+')'!=line_dict[first]: valid = False

        elif re.match(r'^\[impl-in\d+-\d+\]$',reason):
            match = re.search(r'\d+-',reason)
            first = int(reason[match.start():match.end()-1])
            match = re.search(r'\d+\]',reason)
            second = int(reason[match.start():match.end()-1])
            if first>number or second>number or proof[first-3][0]!="[assumption]" or argument!='('+line_dict[first]+'->'+line_dict[second]+')': valid = False

        elif re.match(r'^\[or-el\d+,\d+-\d+,\d+-\d+\]$',reason):
            match = re.search(r'\d+,',reason)
            main = int(reason[match.start():match.end()-1])
            match = re.search(r'\d+-\d+,',reason)
            pair = reason[match.start():match.end()-1].split("-")
            fstart,fend = int(pair[0]),int(pair[1])
            match = re.search(r'\d+-\d+\]',reason)
            pair = reason[match.start():match.end()-1].split("-")
            sstart,send = int(pair[0]),int(pair[1])
            if line_dict[fend]!=argument or line_dict[send]!=argument : valid = False
            if '('+line_dict[fstart]+'\\/'+line_dict[sstart]+')'!=line_dict[main] and '('+line_dict[sstart]+'\\/'+line_dict[fstart]+')'!=line_dict[main]: valid = False
            # for i in range(fstart+1,fend+1):
            # for i in range(sstart+1,send+1):

        else: valid = False

    if valid : return "correct"
    else : return "incorrect"

if __name__ == "__main__":
    filename = sys.argv[1]
    print(checkProof(filename))