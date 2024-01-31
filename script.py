import json 

input_dir = "BookEval/Book/multi-modal/5shot/"
output_dir = "BookEval/lean/multi-modal/5shot/"

def leanFormat(result):
    prediction = result['pred']
    ground = result['gt']
    return f"import SystemE\nimport UniGeo.Relations\n\n\ndef prediction : Prop := {prediction}\n\n\ndef ground : Prop := {ground}\n\nexample : Iff prediction ground := \n by unfold prediction ; unfold ground"

def getJsonData(key):
    with open(input_dir + key , "r") as file:
        result = json.load(file)
        return result

def writeLeanFile(key,contents):
    with open(output_dir + key + ".lean", "w") as file:
        file.write(contents)

toSkip = [2,3,5,6,7,8,12,22,32,10,16,17,18,19,20,42]
def unpack_results():
    for i in range(1,49):
        # if i in toSkip:continue
        result = getJsonData(f'{i}.json')
        asLean = leanFormat(result)        
        writeLeanFile(f'proposition_{i}',asLean)

unpack_results()