sig UserProfile { 
  portrait: disj one Photo
}
sig Album {
  photos: disj set Photo
} {
  #photos > 0
}

sig Photo { 
  photoable_type: one PR_PhotoableTypeField
  // photable_id は定義しない。
}

abstract sig PR_PhotoableTypeField {
  photos_identify: one Photo
}
sig UserProfile_Photoable extends PR_PhotoableTypeField { 
  user_profile: disj one UserProfile
}
sig Album_Photoable extends PR_PhotoableTypeField { 
  album: some Album
}

fact {
  photoable_type = ~photos_identify
  portrait = ~(photoable_type.user_profile)
  photos = ~(photoable_type.album)
}

run {} // for 4 but 8 Photo
