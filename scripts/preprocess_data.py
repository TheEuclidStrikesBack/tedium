import os
import re
import random
import pickle
import numpy as np
from PIL import Image


def main():
    random.seed(42)
    
    with open('proving_test.pk', 'rb') as f:
        dataset = pickle.load(f)

    keys = ['parallel', 'triangle', 'congruent', 'quadrilateral', 'similarity']
    dict = {key: [] for key in keys}

    for idx, sample in enumerate(dataset):
        # follow the setting in UniGeo
        if sample['problem_type'] == 'proportions':
            problem_type = 'triangle'
        else:
            problem_type = sample['problem_type']
        
        dict[problem_type].append(idx)

    for key in keys:
        os.makedirs(key, exist_ok=True)
        sampled_idx = sorted(random.sample(dict[key], 20))

        for i, idx in enumerate(sampled_idx):
            os.makedirs(f'{key}/{i+1}/', exist_ok=True)
            sample = dataset[idx]
            
            # clean input text
            input_text = sample['input_text']
            input_text = re.sub(r'\(Elements:.*?\)', '', input_text).strip()
            input_text = re.sub(r'\s+\.', '.', input_text)

            sentences = input_text.split(". ")
            sentences = [s for s in sentences if not any(s in other for other in sentences if s != other)]
            input_text = '. '.join(sentences)

            with open(f'{key}/{i+1}/text.txt', 'w') as f:
                f.write(input_text)
            
            img = sample['img']
            img = Image.fromarray(img, 'RGB')
            img.save(f'{key}/{i+1}/img.png')

            proof_text = sample['statement']

            with open(f'{key}/{i+1}/proof.txt', 'w') as file:
                for t in proof_text:
                    t = re.sub(r'm∠', '∠', t)
                    file.write(t + '\n')


if __name__ == "__main__":
    main()